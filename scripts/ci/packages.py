"""Discover Lean 4 Lake packages, compute CI matrices, and run strict builds."""

from __future__ import annotations

import argparse
import json
import os
import posixpath
import subprocess
import sys
import tomllib
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterable

REPO_ROOT = Path(__file__).resolve().parents[2]
CANARY_PACKAGE = "26-unit-fractions"
EXCLUDED_ROOT_DIRS: frozenset[str] = frozenset(
    {".git", ".lake", ".ruff_cache", ".venv", "lake-compat"}
)
HEAVY_PACKAGES: frozenset[str] = frozenset(
    {
        "E1486-order-15",
        "E670-order-10",
        "E677-E255-order-9",
        "three-color-t-boards",
    }
)
EXTRA_BUILD_TARGETS: dict[str, tuple[str, ...]] = {
    "three-color-t-boards": (
        "ExactSymmetry",
        "ExactOrbit",
        "MarginalCounterexample",
        "ExactMarginals",
        "ExactParity",
        "ExactNativeMoments",
    ),
}
CI_TRIGGER_PATHS: tuple[str, ...] = (
    ".github/workflows/ci.yml",
    "scripts/ci/",
)
ZERO_SHA = "0" * 40


@dataclass(frozen=True, slots=True)
class LeanPackage:
    """Metadata for a single Lean 4 Lake package in the repository."""

    path: str
    toolchain: str
    uses_mathlib_cache: bool
    heavy: bool
    local_deps: tuple[str, ...]
    default_targets: tuple[str, ...]
    extra_targets: tuple[str, ...]
    lib_roots: tuple[str, ...]


def _extract_lib_roots(lakefile_data: dict[str, object]) -> tuple[str, ...]:
    libs = lakefile_data.get("lean_lib", [])
    if not isinstance(libs, list):
        return ()
    roots: list[str] = []
    for lib in libs:
        if not isinstance(lib, dict):
            continue
        explicit_roots = lib.get("roots")
        if isinstance(explicit_roots, list) and explicit_roots:
            for item in explicit_roots:
                if isinstance(item, str) and item not in roots:
                    roots.append(item)
        else:
            name = lib.get("name")
            if isinstance(name, str) and name not in roots:
                roots.append(name)
    return tuple(roots)


def _extract_local_deps(
    pkg_rel: str, lakefile_data: dict[str, object]
) -> tuple[str, ...]:
    requires = lakefile_data.get("require", [])
    if not isinstance(requires, list):
        return ()
    deps: list[str] = []
    for req in requires:
        if not isinstance(req, dict):
            continue
        raw_path = req.get("path")
        if isinstance(raw_path, str):
            norm = posixpath.normpath(posixpath.join(pkg_rel, raw_path))
            if norm not in deps:
                deps.append(norm)
    return tuple(deps)


def _manifest_has_mathlib(manifest_path: Path) -> bool:
    if not manifest_path.is_file():
        return False
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    packages = data.get("packages", [])
    if not isinstance(packages, list):
        return False
    return any(
        isinstance(entry, dict) and entry.get("name") == "mathlib" for entry in packages
    )


def discover_packages(repo_root: Path = REPO_ROOT) -> dict[str, LeanPackage]:
    """Discover all tracked Lean 4 Lake packages under ``repo_root``."""
    packages: dict[str, LeanPackage] = {}
    for current, dirs, files in os.walk(repo_root):
        rel_dir = Path(current).relative_to(repo_root)
        dirs[:] = sorted(
            d
            for d in dirs
            if d not in EXCLUDED_ROOT_DIRS
            and d != ".lake"
            and d != "__pycache__"
            and not (rel_dir == Path() and d in EXCLUDED_ROOT_DIRS)
        )
        if "lean-toolchain" not in files or "lakefile.toml" not in files:
            continue
        if rel_dir == Path():
            continue
        pkg_rel = rel_dir.as_posix()
        toolchain = (
            (Path(current) / "lean-toolchain").read_text(encoding="utf-8").strip()
        )
        lakefile_data = tomllib.loads(
            (Path(current) / "lakefile.toml").read_text(encoding="utf-8")
        )
        raw_defaults = lakefile_data.get("defaultTargets", [])
        default_targets = (
            tuple(t for t in raw_defaults if isinstance(t, str))
            if isinstance(raw_defaults, list)
            else ()
        )
        packages[pkg_rel] = LeanPackage(
            path=pkg_rel,
            toolchain=toolchain,
            uses_mathlib_cache=_manifest_has_mathlib(
                Path(current) / "lake-manifest.json"
            ),
            heavy=pkg_rel in HEAVY_PACKAGES,
            local_deps=_extract_local_deps(pkg_rel, lakefile_data),
            default_targets=default_targets,
            extra_targets=EXTRA_BUILD_TARGETS.get(pkg_rel, ()),
            lib_roots=_extract_lib_roots(lakefile_data),
        )
    return dict(sorted(packages.items()))


def _owner_package(file_path: str, package_paths: Iterable[str]) -> str | None:
    norm = file_path.strip().removeprefix("./")
    best: str | None = None
    for pkg in package_paths:
        if (norm == pkg or norm.startswith(f"{pkg}/")) and (
            best is None or len(pkg) > len(best)
        ):
            best = pkg
    return best


def affected_packages(
    packages: dict[str, LeanPackage],
    changed_files: Iterable[str],
) -> list[str]:
    """Return sorted packages affected by ``changed_files`` (including dependents)."""
    changed_list = [f.strip().removeprefix("./") for f in changed_files if f.strip()]
    direct: set[str] = set()
    for changed in changed_list:
        owner = _owner_package(changed, packages)
        if owner is not None:
            direct.add(owner)

    if not direct:
        ci_touched = any(
            any(
                changed == prefix or changed.startswith(prefix)
                for prefix in CI_TRIGGER_PATHS
            )
            for changed in changed_list
        )
        if ci_touched and CANARY_PACKAGE in packages:
            return [CANARY_PACKAGE]
        return []

    reverse_deps: dict[str, list[str]] = {pkg: [] for pkg in packages}
    for pkg_path, pkg in packages.items():
        for dep in pkg.local_deps:
            if dep in reverse_deps:
                reverse_deps[dep].append(pkg_path)

    selected: set[str] = set(direct)
    queue: deque[str] = deque(sorted(direct))
    while queue:
        current = queue.popleft()
        for dependent in reverse_deps.get(current, ()):
            if dependent not in selected:
                selected.add(dependent)
                queue.append(dependent)
    return sorted(selected)


def git_changed_files(repo_root: Path, base: str, head: str) -> list[str]:
    """Return paths changed between ``base`` and ``head``."""
    if not base or base == ZERO_SHA:
        parent_check = subprocess.run(
            ["git", "rev-parse", "--verify", f"{head}~1"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=False,
        )
        if parent_check.returncode == 0:
            cmd = ["git", "diff", "--name-only", f"{head}~1", head]
        else:
            cmd = [
                "git",
                "diff-tree",
                "--no-commit-id",
                "--name-only",
                "-r",
                head,
            ]
    else:
        cmd = ["git", "diff", "--name-only", f"{base}...{head}"]
        res = subprocess.run(
            cmd,
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=False,
        )
        if res.returncode == 0:
            return res.stdout.splitlines()
        cmd = ["git", "diff", "--name-only", base, head]

    out = subprocess.check_output(cmd, cwd=repo_root, text=True)
    return out.splitlines()


def build_matrix(
    packages: dict[str, LeanPackage],
    selected: Iterable[str],
) -> list[dict[str, object]]:
    """Build GitHub Actions matrix entries for the selected packages."""
    entries: list[dict[str, object]] = []
    for pkg_path in selected:
        if pkg_path not in packages:
            msg = f"Unknown Lean package: {pkg_path}"
            raise ValueError(msg)
        pkg = packages[pkg_path]
        entries.append(
            {
                "pkg": pkg.path,
                "toolchain": pkg.toolchain,
                "mathlib": pkg.uses_mathlib_cache,
                "heavy": pkg.heavy,
                "timeout_minutes": 180 if pkg.heavy else 45,
            }
        )
    return entries


def _run_cmd(cmd: list[str], cwd: Path) -> None:
    print(f"+ ({cwd}) {' '.join(cmd)}", flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def run_build(
    repo_root: Path,
    pkg_path: str,
    *,
    run_leanchecker: bool = False,
) -> None:
    """Strictly build a Lean package with warnings treated as errors."""
    packages = discover_packages(repo_root)
    if pkg_path not in packages:
        msg = f"Unknown Lean package: {pkg_path}"
        raise SystemExit(msg)
    pkg = packages[pkg_path]
    pkg_dir = repo_root / pkg.path

    if pkg.uses_mathlib_cache:
        _run_cmd(["lake", "exe", "cache", "get"], cwd=pkg_dir)

    _run_cmd(["lake", "--wfail", "build"], cwd=pkg_dir)

    if pkg.extra_targets:
        _run_cmd(["lake", "--wfail", "build", *pkg.extra_targets], cwd=pkg_dir)

    if run_leanchecker and pkg.path == "erdos-64-power-of-two-cycles":
        # Lean 4.36 segfaults during the per-module replay. Erdos64 imports
        # the entire package, so a fresh replay checks all its declarations.
        _run_cmd(["lake", "env", "leanchecker", "--fresh", "Erdos64"], cwd=pkg_dir)
    elif run_leanchecker and not pkg.heavy and pkg.lib_roots:
        _run_cmd(["lake", "env", "leanchecker", *pkg.lib_roots], cwd=pkg_dir)


def _write_github_outputs(path: Path, entries: list[dict[str, object]]) -> None:
    matrix_json = json.dumps({"include": entries}, separators=(",", ":"))
    has_packages = "true" if entries else "false"
    with path.open("a", encoding="utf-8") as handle:
        handle.write(f"matrix={matrix_json}\n")
        handle.write(f"has_packages={has_packages}\n")
        handle.write(f"count={len(entries)}\n")


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    matrix_parser = subparsers.add_parser(
        "matrix", help="Compute a GitHub Actions matrix of Lean packages."
    )
    matrix_parser.add_argument(
        "--mode",
        choices=("changed", "standard", "heavy", "all"),
        required=True,
    )
    matrix_parser.add_argument("--base", default="")
    matrix_parser.add_argument("--head", default="HEAD")
    matrix_parser.add_argument(
        "--filter",
        default="",
        help="Optional comma-separated package paths overriding --mode selection.",
    )
    matrix_parser.add_argument("--github-output", type=Path, default=None)

    build_parser = subparsers.add_parser(
        "build", help="Strictly build one Lean package."
    )
    build_parser.add_argument("package", help="Relative path to the Lake package.")
    build_parser.add_argument(
        "--leanchecker",
        action="store_true",
        help="Run bundled `lake env leanchecker` on non-heavy package library roots.",
    )

    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint."""
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    if args.command == "build":
        run_build(REPO_ROOT, args.package, run_leanchecker=args.leanchecker)
        return 0

    packages = discover_packages(REPO_ROOT)
    filter_raw = str(args.filter).strip()
    if filter_raw:
        selected = [p.strip() for p in filter_raw.split(",") if p.strip()]
    elif args.mode == "changed":
        changed = git_changed_files(REPO_ROOT, args.base, args.head)
        selected = affected_packages(packages, changed)
    elif args.mode == "standard":
        selected = [p for p, info in packages.items() if not info.heavy]
    elif args.mode == "heavy":
        selected = [p for p, info in packages.items() if info.heavy]
    else:
        selected = list(packages)

    entries = build_matrix(packages, selected)
    if args.github_output is not None:
        _write_github_outputs(args.github_output, entries)
    print(json.dumps({"include": entries}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
