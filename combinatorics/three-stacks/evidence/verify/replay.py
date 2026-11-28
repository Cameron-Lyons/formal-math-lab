"""Replay the stored one-card-deletion certificates using Python alone."""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Sequence

PANTONE_VATTER = [
    6,
    3,
    12,
    8,
    17,
    5,
    2,
    11,
    7,
    19,
    14,
    10,
    4,
    18,
    13,
    21,
    16,
    9,
    20,
    15,
    1,
]


def replay(deck: Sequence[int], word: str) -> bool:
    """Replay a 4-station transfer word and check whether it sorts ``deck``."""
    stacks: list[list[int]] = [list(reversed(deck)), [], [], [], []]
    for step in map(int, word):
        if step not in range(1, 5) or not stacks[step - 1]:
            raise ValueError("Invalid operation")
        stacks[step].append(stacks[step - 1].pop())
    return all(not stack for stack in stacks[:-1]) and stacks[-1] == sorted(deck)


if __name__ == "__main__":
    path = Path(__file__).with_name("published") / "deletions.txt"
    _header, *lines = path.read_text(encoding="utf-8").splitlines()
    seen: set[int] = set()
    for line in lines:
        label, word = line.split(": ")
        verb, value_str = label.split()
        value = int(value_str)
        if verb != "delete" or value not in PANTONE_VATTER or value in seen:
            raise ValueError(f"Unexpected certificate label: {label}")
        deck = [x for x in PANTONE_VATTER if x != value]
        if not replay(deck, word):
            raise ValueError(f"Invalid certificate for deletion of {value}")
        seen.add(value)
    if len(seen) != len(PANTONE_VATTER):
        raise ValueError("Missing one-card-deletion certificate")
    print(f"Replayed all {len(seen)} one-card deletions.")
