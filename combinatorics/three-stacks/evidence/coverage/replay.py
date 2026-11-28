"""Check that every residual input has exactly one valid saved schedule."""

from __future__ import annotations

import gzip
import sys
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterable

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify.replay import replay


def validate(residuals: Iterable[str], certificates: Iterable[str]) -> None:
    """Verify a bijection between residual decks and valid sorting schedules."""
    pending: set[tuple[int, ...]] = set()
    for line in residuals:
        tag, status, *cards = line.split()
        deck = tuple(map(int, cards))
        if tag != "Hard" or status != "1" or deck in pending:
            raise ValueError("Invalid or duplicate residual input")
        pending.add(deck)
    count = len(pending)
    for line in certificates:
        *cards, word = line.split()
        deck = tuple(map(int, cards))
        if deck not in pending or len(word) != 4 * len(deck) or not replay(deck, word):
            raise ValueError("Unmatched input or invalid sorting schedule")
        pending.remove(deck)
    if pending:
        raise ValueError(f"{len(pending)} residual inputs lack a sorting schedule")
    print(f"Verified all {count} residual sorting schedules")


if __name__ == "__main__":
    with (
        Path(sys.argv[1]).open(encoding="utf-8") as rows,
        gzip.open(sys.argv[2], "rt", encoding="utf-8") as words,
    ):
        validate(rows, words)
