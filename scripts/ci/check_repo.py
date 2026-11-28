"""Strict static integrity checks for the repository and all Lean 4 proofs."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import TYPE_CHECKING

from scripts.ci.packages import (
    EXTRA_LEAN_CHECK_FILES,
    REPO_ROOT,
    LeanPackage,
    discover_packages,
)

if TYPE_CHECKING:
    from collections.abc import Iterable

TOOLCHAIN_RE = re.compile(r"^leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?$")
GIT_SHA_RE = re.compile(r"^[0-9a-f]{40}$")
FORBIDDEN_WORD_RE = re.compile(r"\b(sorry|admit)\b")
AXIOM_DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*axiom\s+([^\s:(]+)"
)
UNSAFE_DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*unsafe\s+"
    r"(?:def|theorem|axiom|opaque|instance|structure|inductive)\b"
)
TRUST_ATTR_RE = re.compile(r"@\[[^\]]*\b(?:implemented_by|extern)\b")
LEAN_IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+?)(?:\s*--.*)?$"
)
MD_LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

# Explicitly documented external-certificate axioms permitted in the repository.
ALLOWED_AXIOMS: frozenset[tuple[str, str]] = frozenset(
    {
        (
            "combinatorics/queen-domination-48/sat/Certified48.lean",
            "formulas_48_24_unsat",
        ),
    }
)

FORBIDDEN_ARTIFACT_SUFFIXES: tuple[str, ...] = (
    ".olean",
    ".ilean",
    ".o",
    ".a",
    ".so",
    ".pyc",
)
FORBIDDEN_PATH_PARTS: frozenset[str] = frozenset(
    {".lake", ".ruff_cache", "__pycache__", ".venv", ".DS_Store"}
)


def strip_lean_comments_and_strings(source: str) -> str:
    """Remove Lean line comments, nested block comments, and string literals.

    Newlines are preserved so line numbers match the original source.
    """
    out: list[str] = []
    i = 0
    n = len(source)
    block_depth = 0
    in_string = False

    while i < n:
        ch = source[i]
        nxt = source[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                i += 1
        elif in_string:
            if ch == "\\" and i + 1 < n:
                if nxt == "\n":
                    out.append("\n")
                i += 2
            elif ch == '"':
                in_string = False
                out.append('""')
                i += 1
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                i += 1
        elif ch == "-" and nxt == "-":
            while i < n and source[i] != "\n":
                i += 1
        elif ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
        elif ch == '"':
            in_string = True
            i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def scan_lean_source(
    rel_path: str,
    source: str,
    *,
    allowed_axioms: frozenset[tuple[str, str]] = ALLOWED_AXIOMS,
) -> tuple[list[str], set[tuple[str, str]]]:
    """Check one Lean source file for forbidden constructs."""
    errors: list[str] = []
    seen_allowed: set[tuple[str, str]] = set()
    stripped = strip_lean_comments_and_strings(source)

    for lineno, line in enumerate(stripped.splitlines(), 1):
        errors.extend(
            f"{rel_path}:{lineno}: forbidden proof placeholder `{match.group(1)}`"
            for match in FORBIDDEN_WORD_RE.finditer(line)
        )

        axiom_match = AXIOM_DECL_RE.match(line)
        if axiom_match is not None:
            key = (rel_path, axiom_match.group(1))
            if key in allowed_axioms:
                seen_allowed.add(key)
            else:
                errors.append(
                    f"{rel_path}:{lineno}: unallowlisted axiom `{axiom_match.group(1)}`"
                )

        if UNSAFE_DECL_RE.match(line):
            errors.append(f"{rel_path}:{lineno}: forbidden `unsafe` declaration")

        if TRUST_ATTR_RE.search(line):
            errors.append(
                f"{rel_path}:{lineno}: forbidden `@[implemented_by]` or `@[extern]` attribute"
            )

    return errors, seen_allowed


def extract_lean_imports(source: str) -> list[str]:
    """Return imported module names from a Lean 4 source file."""
    imports: list[str] = []
    for line in source.splitlines():
        match = LEAN_IMPORT_RE.match(line)
        if match is None:
            continue
        for tok in match.group(1).split():
            if tok.startswith("--"):
                break
            if tok not in {"public", "private", "meta", "all"}:
                imports.append(tok)
    return imports


def check_markdown_links(repo_root: Path, tracked: Iterable[str]) -> list[str]:
    """Verify that every relative Markdown link in tracked `.md` files resolves."""
    errors: list[str] = []
    for rel in sorted(tracked):
        if not rel.endswith(".md"):
            continue
        md_path = repo_root / rel
        if not md_path.is_file():
            continue
        text = md_path.read_text(encoding="utf-8", errors="replace")
        for lineno, line in enumerate(text.splitlines(), 1):
            for match in MD_LINK_RE.finditer(line):
                target = match.group(1).strip()
                if target.startswith(("http://", "https://", "mailto:", "#")):
                    continue
                path_part = target.split("#", 1)[0]
                if not path_part:
                    continue
                resolved = (md_path.parent / path_part).resolve()
                if not resolved.exists():
                    errors.append(
                        f"{rel}:{lineno}: broken relative Markdown link `{target}`"
                    )
    return errors


def check_lean_reachability(
    repo_root: Path,
    packages: dict[str, LeanPackage],
    tracked: Iterable[str],
) -> list[str]:
    """Verify every tracked `.lean` file in a Lake package is reachable by CI builds."""
    errors: list[str] = []
    tracked_lean = [rel for rel in tracked if rel.endswith(".lean")]

    for pkg_rel in sorted(packages):
        pkg_dir = repo_root / pkg_rel
        lf_data = tomllib.loads((pkg_dir / "lakefile.toml").read_text(encoding="utf-8"))
        nested_pkgs = [
            other
            for other in packages
            if other != pkg_rel and other.startswith(f"{pkg_rel}/")
        ]
        pkg_lean = [
            rel
            for rel in tracked_lean
            if rel.startswith(f"{pkg_rel}/")
            and not any(rel.startswith(f"{np}/") for np in nested_pkgs)
        ]

        src_dirs: set[str] = {str(lf_data.get("srcDir", ""))}
        libs = lf_data.get("lean_lib", [])
        exes = lf_data.get("lean_exe", [])
        if isinstance(libs, list):
            for lib in libs:
                if isinstance(lib, dict) and isinstance(lib.get("srcDir"), str):
                    src_dirs.add(lib["srcDir"])
        if isinstance(exes, list):
            for exe in exes:
                if isinstance(exe, dict) and isinstance(exe.get("srcDir"), str):
                    src_dirs.add(exe["srcDir"])

        mod_to_file: dict[str, str] = {}
        for rel in pkg_lean:
            sub = rel[len(pkg_rel) + 1 :]
            matched = False
            for sd in sorted(src_dirs, key=len, reverse=True):
                prefix = f"{sd.rstrip('/')}/" if sd else ""
                if not prefix or sub.startswith(prefix):
                    mod = sub[len(prefix) : -5].replace("/", ".")
                    mod_to_file[mod] = rel
                    matched = True
            if not matched:
                mod_to_file[sub[:-5].replace("/", ".")] = rel

        seeds: set[str] = set()
        defaults = lf_data.get("defaultTargets", [])
        default_names = (
            {t for t in defaults if isinstance(t, str)}
            if isinstance(defaults, list)
            else set()
        )

        if isinstance(libs, list):
            for lib in libs:
                if not isinstance(lib, dict) or lib.get("name") not in default_names:
                    continue
                explicit_roots = lib.get("roots")
                if isinstance(explicit_roots, list) and explicit_roots:
                    for item in explicit_roots:
                        if isinstance(item, str) and item in mod_to_file:
                            seeds.add(mod_to_file[item])
                elif isinstance(lib.get("name"), str) and lib["name"] in mod_to_file:
                    seeds.add(mod_to_file[lib["name"]])
                globs = lib.get("globs")
                if isinstance(globs, list):
                    for g in globs:
                        if not isinstance(g, str):
                            continue
                        if g.endswith(".+"):
                            pref = g[:-2]
                            for m, f in mod_to_file.items():
                                if m == pref or m.startswith(f"{pref}."):
                                    seeds.add(f)
                        elif g.endswith(".*"):
                            pref = g[:-2]
                            for m, f in mod_to_file.items():
                                if (
                                    m.startswith(f"{pref}.")
                                    and "." not in m[len(pref) + 1 :]
                                ):
                                    seeds.add(f)
                        elif g in mod_to_file:
                            seeds.add(mod_to_file[g])

        if isinstance(exes, list):
            for exe in exes:
                if not isinstance(exe, dict) or exe.get("name") not in default_names:
                    continue
                root_mod = exe.get("root", exe.get("name"))
                if isinstance(root_mod, str) and root_mod in mod_to_file:
                    seeds.add(mod_to_file[root_mod])

        for extra_file in EXTRA_LEAN_CHECK_FILES.get(pkg_rel, ()):
            extra_rel = f"{pkg_rel}/{extra_file}"
            if extra_rel in pkg_lean:
                seeds.add(extra_rel)

        # Also include modules imported by local dependent packages.
        for other_rel, other_pkg in packages.items():
            if pkg_rel not in other_pkg.local_deps:
                continue
            other_nested = [
                o for o in packages if o != other_rel and o.startswith(f"{other_rel}/")
            ]
            for rel in tracked_lean:
                if rel.startswith(f"{other_rel}/") and not any(
                    rel.startswith(f"{np}/") for np in other_nested
                ):
                    src = (repo_root / rel).read_text(
                        encoding="utf-8", errors="replace"
                    )
                    for imp in extract_lean_imports(src):
                        if imp in mod_to_file:
                            seeds.add(mod_to_file[imp])

        visited: set[str] = set()
        stack = list(seeds)
        while stack:
            cur = stack.pop()
            if cur in visited:
                continue
            visited.add(cur)
            src = (repo_root / cur).read_text(encoding="utf-8", errors="replace")
            for imp in extract_lean_imports(src):
                target = mod_to_file.get(imp)
                if target is not None and target not in visited:
                    stack.append(target)

        errors.extend(
            f"{orphan}: Lean module is unreachable from `{pkg_rel}` default targets"
            for orphan in sorted(set(pkg_lean) - visited)
        )

    return errors


def _git_tracked_files(repo_root: Path) -> list[str]:
    out = subprocess.check_output(
        ["git", "ls-files", "-z"],
        cwd=repo_root,
    )
    return [p for p in out.decode("utf-8").split("\0") if p]


def check_repository(repo_root: Path = REPO_ROOT) -> list[str]:
    """Run all strict static repository and Lean proof checks."""
    errors: list[str] = []
    tracked = _git_tracked_files(repo_root)
    tracked_set = set(tracked)

    # 1. Root Python config checks.
    pyproject_path = repo_root / "pyproject.toml"
    if not pyproject_path.is_file():
        errors.append("pyproject.toml: missing root project configuration")
    else:
        try:
            tomllib.loads(pyproject_path.read_text(encoding="utf-8"))
        except tomllib.TOMLDecodeError as exc:
            errors.append(f"pyproject.toml: invalid TOML ({exc})")
    if "uv.lock" not in tracked_set:
        errors.append("uv.lock: lockfile must be tracked in git")

    # 2. Forbidden tracked artifacts and broken symlinks.
    for rel in tracked:
        full = repo_root / rel
        parts = Path(rel).parts
        if any(part in FORBIDDEN_PATH_PARTS for part in parts):
            errors.append(f"{rel}: forbidden build/cache path tracked in git")
        if rel.endswith(FORBIDDEN_ARTIFACT_SUFFIXES):
            errors.append(f"{rel}: forbidden compiled artifact tracked in git")
        if full.is_symlink() and not full.exists():
            errors.append(f"{rel}: broken symlink tracked in git")

    # 3. Lean package metadata, manifests, toolchains, and README coverage.
    readme_text = (repo_root / "README.md").read_text(encoding="utf-8")
    packages = discover_packages(repo_root)
    if not packages:
        errors.append("No Lean packages discovered in repository")

    for pkg_rel, pkg in packages.items():
        pkg_dir = repo_root / pkg_rel
        if not TOOLCHAIN_RE.fullmatch(pkg.toolchain):
            errors.append(
                f"{pkg_rel}/lean-toolchain: invalid pinned toolchain `{pkg.toolchain}`"
            )

        lakefile_path = pkg_dir / "lakefile.toml"
        try:
            lf_data = tomllib.loads(lakefile_path.read_text(encoding="utf-8"))
            if not isinstance(lf_data.get("name"), str) or not lf_data["name"]:
                errors.append(f"{pkg_rel}/lakefile.toml: missing non-empty `name`")
        except tomllib.TOMLDecodeError as exc:
            errors.append(f"{pkg_rel}/lakefile.toml: invalid TOML ({exc})")

        manifest_path = pkg_dir / "lake-manifest.json"
        if not manifest_path.is_file():
            errors.append(f"{pkg_rel}/lake-manifest.json: missing manifest")
        else:
            try:
                manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                errors.append(f"{pkg_rel}/lake-manifest.json: invalid JSON ({exc})")
            else:
                for dep in manifest.get("packages", []):
                    if not isinstance(dep, dict):
                        continue
                    if dep.get("type") == "git":
                        rev = dep.get("rev", "")
                        if not isinstance(rev, str) or not GIT_SHA_RE.fullmatch(rev):
                            errors.append(
                                f"{pkg_rel}/lake-manifest.json: dependency "
                                f"`{dep.get('name')}` has unpinned rev `{rev}`"
                            )

        errors.extend(
            f"{pkg_rel}/lakefile.toml: local path dependency `{dep_path}` "
            "does not resolve to a Lean package"
            for dep_path in pkg.local_deps
            if dep_path not in packages
        )

        errors.extend(
            f"{pkg_rel}/{extra_file}: configured EXTRA_LEAN_CHECK_FILES entry missing"
            for extra_file in pkg.extra_check_files
            if not (pkg_dir / extra_file).is_file()
        )

        is_nested_subpkg = any(
            other != pkg_rel and pkg_rel.startswith(f"{other}/") for other in packages
        )
        if not is_nested_subpkg and not (
            (pkg_dir / "README.md").is_file()
            or (pkg_dir.parent / "README.md").is_file()
        ):
            errors.append(f"{pkg_rel}/README.md: missing package README")

        if pkg_rel not in readme_text:
            errors.append(f"README.md: Lean package `{pkg_rel}` is not listed")

    # 4. Strict Lean proof hygiene across every tracked .lean file.
    lean_files = sorted(rel for rel in tracked if rel.endswith(".lean"))
    seen_allowed_axioms: set[tuple[str, str]] = set()
    for rel in lean_files:
        source = (repo_root / rel).read_text(encoding="utf-8", errors="replace")
        file_errors, file_allowed = scan_lean_source(rel, source)
        errors.extend(file_errors)
        seen_allowed_axioms.update(file_allowed)

    stale_axioms = sorted(ALLOWED_AXIOMS - seen_allowed_axioms)
    for rel, name in stale_axioms:
        errors.append(
            f"scripts/ci/check_repo.py: stale ALLOWED_AXIOMS entry `{rel}:{name}`"
        )

    # 5. Unreachable Lean modules and broken relative Markdown links.
    errors.extend(check_lean_reachability(repo_root, packages, tracked))
    errors.extend(check_markdown_links(repo_root, tracked))

    return errors


def main() -> int:
    """CLI entrypoint."""
    errors = check_repository(REPO_ROOT)
    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        print(
            f"\nRepository integrity check failed with {len(errors)} error(s).",
            file=sys.stderr,
        )
        return 1

    packages = discover_packages(REPO_ROOT)
    lean_count = sum(1 for p in _git_tracked_files(REPO_ROOT) if p.endswith(".lean"))
    print(
        f"Repository integrity OK: {len(packages)} Lean packages, "
        f"{lean_count} Lean files, 0 violations."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
