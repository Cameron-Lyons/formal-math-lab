"""Verify all six observed length-18 rank progressions, counts, and schedules."""

from __future__ import annotations

import gzip
import re
import sys
import tarfile
import tempfile
from math import comb, factorial
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coverage.replay import validate

EVIDENCE_DIR = Path(__file__).resolve().parents[1]
ROOT = Path(__file__).resolve().parent / "results"
RESULTS_ARCHIVE = EVIDENCE_DIR / "results.tar.gz"
PARTS = ("0", "1", "2a", "3a", "2b", "3b")
SETS = comb(17, 7)
HEADS = factorial(10)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def require_match(pattern: str, text: str, *, flags: int = 0) -> re.Match[str]:
    match = re.search(pattern, text, flags)
    if match is None:
        raise ValueError(f"Expected pattern {pattern!r} not found")
    return match


def fields(line: str, names: Sequence[str]) -> list[int]:
    words = line.split()
    return [int(words[words.index(key) + 1]) for key in names]


def read_progress(directory: Path, ranks: range, canonical: bool) -> list[int]:
    tag = "Through rank " if canonical else "through "
    with gzip.open(directory / "progress.txt.gz", "rt", encoding="utf-8") as file:
        lines = [line for line in file if line.startswith(tag)]
    chunk = 8 if canonical else 1
    endpoints = [min(i + chunk, len(ranks)) for i in range(0, len(ranks), chunk)]
    require(len(lines) == len(endpoints), f"{directory}: missing progress records")
    with gzip.open(
        directory / "residual-counts.txt.gz", "rt", encoding="utf-8"
    ) as file:
        raw = [tuple(map(int, line.split())) for line in file]
    require(
        len(raw) == len(ranks)
        and all(
            rank == observed and count >= 0
            for rank, (observed, count) in zip(ranks, raw, strict=True)
        ),
        f"{directory}: incorrect ranks in the residual stream",
    )
    previous = [0, 0]
    raw_done = 0
    raw_count = 0
    for line, done in zip(lines, endpoints, strict=True):
        last, blocks, missed, pending = fields(
            line,
            [
                "rank" if canonical else "through",
                "blocks",
                "disjoint" if canonical else "no_common",
                "pending",
            ],
        )
        require(
            last == ranks[done - 1] and blocks == done * SETS,
            f"{directory}: incorrect rank progression at {last}",
        )
        raw_count += sum(count for _, count in raw[raw_done:done])
        raw_done = done
        require(
            raw_count == pending, f"{directory}: residual stream differs at rank {last}"
        )
        require(
            missed >= previous[0] and pending >= previous[1] and pending <= missed,
            f"{directory}: inconsistent cumulative progress at {last}",
        )
        if not canonical:
            decks, bond, dual = fields(line, ["decks", "bonds", "dual"])
            require(
                decks == blocks * HEADS and missed == bond + dual + pending,
                f"{directory}: incorrect intermediate count at {last}",
            )
        previous = [missed, pending]
    return previous


def suffix_rank(cards: Sequence[int]) -> int:
    rank = 0
    for i, v in enumerate(cards):
        rank = rank * (i + 1) + sum(w > v for w in cards[:i])
    return rank


def audit(root: Path = ROOT) -> None:
    seen_ranks: list[int] = []
    sums = dict.fromkeys(
        ["decks", "first", "bond", "dual", "symmetry", "recuts", "word"], 0
    )
    for part in PARTS:
        directory = root / f"n18-{part}"
        first_s, stop_s, stride_s, mode = (
            (directory / "range.txt").read_text(encoding="utf-8").split()
        )
        first, stop, stride = map(int, (first_s, stop_s, stride_s))
        require(
            0 <= first < stop <= 5040
            and stride > 0
            and mode in ("standard", "canonical"),
            f"{directory}: invalid declared range",
        )
        batch = range(first, stop, stride)
        seen_ranks.extend(batch)
        canonical = mode == "canonical"
        last_counts = read_progress(directory, batch, canonical)
        term = (directory / "join.txt").read_text(encoding="utf-8")
        if canonical:
            decks = int(require_match(r"Universally enumerated (\d+)", term)[1])
            missed, bond, dual, sym, pending = [
                int(require_match("^" + name + r" (\d+)$", term, flags=re.MULTILINE)[1])
                for name in ["Disjoint", "Bond", "Dual", "By symmetry", "Residual"]
            ]
        else:
            final = [line for line in term.splitlines() if line.startswith("through ")][
                -1
            ]
            last, decks, missed, bond, dual, pending = fields(
                final, ["through", "decks", "no_common", "bonds", "dual", "pending"]
            )
            require(last == batch[-1], f"{directory}: incorrect final rank")
            sym = 0
        require(
            [missed, pending] == last_counts
            and decks == len(batch) * SETS * HEADS
            and missed == bond + dual + sym + pending,
            f"{directory}: join totals differ",
        )
        sums["decks"] += decks
        sums["first"] += decks - missed
        sums["bond"] += bond
        sums["dual"] += dual
        sums["symmetry"] += sym
        for label in ["first", "second", "dual-first", "dual-second"]:
            line = (directory / (label + ".txt")).read_text(encoding="utf-8")
            match = re.fullmatch(
                r"cut (\d+) n 18 cached (\d+) searched (\d+) remaining (\d+) seconds [\d.e+\-]+\n",
                line,
            )
            require(match is not None, f"{directory}: invalid {label} stage")
            assert match is not None
            cut, cached, searched, left = map(int, match.groups())
            require(
                cut == (9 if label.endswith("first") else 8)
                and cached + searched + left == pending,
                f"{directory}: {label} counts differ",
            )
            sums["recuts"] += cached + searched
            pending = left
        with (
            (directory / "individual.txt").open(encoding="utf-8") as src,
            gzip.open(directory / "words.txt.gz", "rt", encoding="utf-8") as words,
        ):
            count = 0
            for line in src:
                p = tuple(map(int, line.split()[2:]))
                require(
                    sorted(p) == list(range(1, 19))
                    and p[-1] == 1
                    and suffix_rank(p[10:-1]) in batch,
                    f"{directory}: invalid residual deck or wrong rank",
                )
                count += 1
            require(count == pending, f"{directory}: wrong number of residuals")
            src.seek(0)
            validate(src, words)
        sums["word"] += pending
    require(
        sorted(seen_ranks) == list(range(5040)),
        "Observed length-18 rank ranges overlap or leave a gap",
    )
    require(
        sums["decks"] == factorial(17)
        and sums["decks"] == sum(v for k, v in sums.items() if k != "decks"),
        "Length-18 totals differ",
    )
    print(sums)


def main() -> None:
    if len(sys.argv) > 2:
        raise SystemExit("Usage: python coverage/audit18.py [results-directory]")
    if len(sys.argv) == 2:
        audit(Path(sys.argv[1]))
    elif ROOT.is_dir():
        audit(ROOT)
    else:
        with tempfile.TemporaryDirectory(prefix="three-stacks-results-") as tmp:
            with tarfile.open(RESULTS_ARCHIVE, "r:gz") as tf:
                tf.extractall(tmp, filter="data")
            audit(Path(tmp) / "coverage" / "results")


if __name__ == "__main__":
    main()
