"""Compile and verify all first-party C23 and C++23 source files strictly."""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

from scripts.ci.packages import REPO_ROOT

THIRD_PARTY_PREFIXES: tuple[str, ...] = ()
THIRD_PARTY_FILES: frozenset[str] = frozenset()
# First-party sources whose builds require external untracked source trees
# (nauty 2.9.3) rather than the repository alone.
EXTERNAL_DEP_FILES: frozenset[str] = frozenset(
    {
        "erdos-64-power-of-two-cycles/scripts/geng_terminals.c",  # Linked into nauty's geng.
    }
)


@dataclass(frozen=True, slots=True)
class SourceClassification:
    """Categorized C and C++ files discovered from git."""

    c_files: tuple[str, ...]
    cpp_files: tuple[str, ...]
    skipped_third_party: tuple[str, ...]
    skipped_external_deps: tuple[str, ...]
    stale_exclusions: tuple[str, ...]


def classify_sources(tracked_files: list[str]) -> SourceClassification:
    """Partition tracked C/C++ source files into checked vs explicitly skipped."""
    tracked_set = set(tracked_files)
    stale = sorted(
        path
        for path in (THIRD_PARTY_FILES | EXTERNAL_DEP_FILES)
        if path not in tracked_set
    )

    c_files: list[str] = []
    cpp_files: list[str] = []
    skipped_third_party: list[str] = []
    skipped_external_deps: list[str] = []

    for rel in sorted(tracked_files):
        if not rel.endswith((".c", ".cpp")):
            continue
        if rel in THIRD_PARTY_FILES or any(
            rel.startswith(prefix) for prefix in THIRD_PARTY_PREFIXES
        ):
            skipped_third_party.append(rel)
        elif rel in EXTERNAL_DEP_FILES:
            skipped_external_deps.append(rel)
        elif rel.endswith(".c"):
            c_files.append(rel)
        else:
            cpp_files.append(rel)

    return SourceClassification(
        c_files=tuple(c_files),
        cpp_files=tuple(cpp_files),
        skipped_third_party=tuple(skipped_third_party),
        skipped_external_deps=tuple(skipped_external_deps),
        stale_exclusions=tuple(stale),
    )


def _git_tracked_c_cpp(repo_root: Path) -> list[str]:
    out = subprocess.check_output(
        ["git", "ls-files", "-z", "*.c", "*.cpp"],
        cwd=repo_root,
    )
    return [p for p in out.decode("utf-8").split("\0") if p]


def _compile_one(
    repo_root: Path,
    rel_path: str,
    compiler: str,
    std: str,
    mode: str,
    extra_link_flags: tuple[str, ...],
    tmp_dir: Path,
    index: int,
) -> tuple[str, int, str]:
    src = repo_root / rel_path
    cmd = [
        compiler,
        f"-std={std}",
        "-O2",
        "-Wall",
        "-Wextra",
        "-Wpedantic",
        "-Werror",
    ]
    if mode == "syntax":
        cmd.extend(["-fsyntax-only", str(src)])
    else:
        out_bin = tmp_dir / f"bin_{index}"
        cmd.extend([str(src), "-o", str(out_bin), *extra_link_flags])

    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    output = (res.stdout + res.stderr).strip()
    return rel_path, res.returncode, output


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cc", default="gcc", help="C23 compiler executable.")
    parser.add_argument("--cxx", default="g++", help="C++23 compiler executable.")
    parser.add_argument(
        "--mode",
        choices=("link", "syntax"),
        default="link",
        help="Compile and link binaries (`link`) or syntax/type check only (`syntax`).",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=max(1, os.cpu_count() or 1),
        help="Maximum parallel compiler invocations.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint."""
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    tracked = _git_tracked_c_cpp(REPO_ROOT)
    classified = classify_sources(tracked)

    if classified.stale_exclusions:
        for stale in classified.stale_exclusions:
            print(
                f"ERROR: stale exclusion in scripts/ci/check_c_cpp.py: {stale}",
                file=sys.stderr,
            )
        return 1

    tasks: list[tuple[str, str, str, tuple[str, ...], int]] = []
    idx = 0
    for rel in classified.c_files:
        tasks.append((rel, args.cc, "c23", ("-lm",), idx))
        idx += 1
    for rel in classified.cpp_files:
        tasks.append((rel, args.cxx, "c++23", ("-pthread",), idx))
        idx += 1

    failures: list[tuple[str, int, str]] = []
    with (
        tempfile.TemporaryDirectory(prefix="formal-math-lab-cc-") as tmp_str,
        ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool,
    ):
        tmp_dir = Path(tmp_str)
        futures = [
            pool.submit(
                _compile_one,
                REPO_ROOT,
                rel,
                compiler,
                std,
                args.mode,
                link_flags,
                tmp_dir,
                item_idx,
            )
            for rel, compiler, std, link_flags, item_idx in tasks
        ]
        for fut in futures:
            rel, code, output = fut.result()
            if code != 0:
                failures.append((rel, code, output))

    if failures:
        for rel, code, output in failures:
            print(f"FAIL ({code}): {rel}\n{output}\n", file=sys.stderr)
        print(
            f"C/C++ strict check failed: {len(failures)}/{len(tasks)} files failed "
            f"(cc={args.cc}, cxx={args.cxx}, mode={args.mode}).",
            file=sys.stderr,
        )
        return 1

    print(
        f"C/C++ strict check OK ({args.cc}/{args.cxx}, mode={args.mode}): "
        f"{len(classified.c_files)} C23 files, {len(classified.cpp_files)} C++23 files "
        f"(skipped {len(classified.skipped_third_party)} third-party, "
        f"{len(classified.skipped_external_deps)} external-dep)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
