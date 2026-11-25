"""Strict static integrity checks for the repository and all Lean 4 proofs."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

from scripts.ci.packages import REPO_ROOT, discover_packages

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

# Explicitly documented external-certificate axioms permitted in the repository.
ALLOWED_AXIOMS: frozenset[tuple[str, str]] = frozenset(
    {
        ("queen-domination-48-sat/Certified48.lean", "formulas_48_24_unsat"),
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
    {".lake", "__pycache__", ".venv", ".DS_Store"}
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

        if "/" not in pkg_rel:
            if not (pkg_dir / "README.md").is_file():
                errors.append(f"{pkg_rel}/README.md: missing top-level package README")
            if f"{pkg_rel}/" not in readme_text:
                errors.append(
                    f"README.md: top-level Lean package `{pkg_rel}/` is not listed"
                )

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
