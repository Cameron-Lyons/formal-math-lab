"""Independently search for 150 points while retaining the seed outside a band of rows.

Run `python search_windows.py 32` to reproduce StripCertificates.lean. On
success the output is a candidate and its Lean verification. Otherwise the
output invokes the Lean proof search for the same width. Progress goes to stderr.
"""

import re
import sys
from functools import lru_cache
from math import gcd
from pathlib import Path

SIDE = 75
BOARD = (1 << (SIDE * SIDE)) - 1


def read_seed():
    source = Path(__file__).with_name("Grid75.lean").read_text()
    literal = source.split("def witness148 : List Point := [", 1)[1].split("]", 1)[0]
    points = [
        int(x) + SIDE * int(y) for x, y in re.findall(r"\((\d+), (\d+)\)", literal)
    ]
    assert len(set(points)) == len(points) == 148
    return points


def coords(p):
    return p % SIDE, p // SIDE


def mask(points):
    return sum(1 << p for p in points)


def members(bits):
    while bits:
        low = bits & -bits
        yield low.bit_length() - 1
        bits ^= low


@lru_cache(maxsize=32768)
def secant(a, b):
    x, y = coords(a)
    u, v = coords(b)
    d = gcd(u - x, v - y)
    dx, dy = (u - x) // d, (v - y) // d
    while 0 <= x - dx < SIDE and 0 <= y - dy < SIDE:
        x -= dx
        y -= dy
    line = 0
    while 0 <= x < SIDE and 0 <= y < SIDE:
        line |= 1 << (SIDE * y + x)
        x += dx
        y += dy
    return line


def select(p, fixed, available):
    assert available & (1 << p)
    unavailable = 1 << p
    for a in fixed:
        unavailable |= secant(min(a, p), max(a, p))
    return available & ~unavailable


LINES = [mask(range(y * SIDE, (y + 1) * SIDE)) for y in range(SIDE)]
LINES += [mask(range(x, SIDE * SIDE, SIDE)) for x in range(SIDE)]


def choose_line(fixed_mask, available):
    best_score = None
    best = None
    for axis, line in enumerate(LINES):
        taken = (fixed_mask & line).bit_count()
        if taken >= 2:
            continue
        free = line & available
        count = free.bit_count()
        slack = count + taken - 2
        # Prefer an immediate contradiction, then the smallest branching set.
        score = (0, count) if slack < 0 else (1, slack, count)
        if best_score is None or score < best_score:
            best_score = score
            best = (axis, fixed_mask & line, free)
    assert best is not None
    return best


class Found(Exception):
    pass


def search(fixed, fixed_mask, available):
    """Each node tries all required cells on a most constrained line."""
    if len(fixed) == 150:
        raise Found(fixed)
    _, taken, free = choose_line(fixed_mask, available)
    candidates = list(members(free))
    if not taken and candidates:
        candidates.pop()  # A complete line uses two cells, so one may be exempted.
    nodes = 1
    for p in candidates:
        nodes += search([*fixed, p], fixed_mask | (1 << p), select(p, fixed, available))
    return nodes


def run(width):
    if not 0 <= width <= 74:
        raise ValueError("width must be between 0 and 74")
    seed = read_seed()
    for first in range(SIDE - width):
        fixed = [p for p in seed if not first <= p // SIDE < first + width]
        available = BOARD
        for i, p in enumerate(fixed):
            available = select(p, fixed[:i], available)
        nodes = search(fixed, mask(fixed), available)
        print(f"window {first}, {nodes} refutation nodes", file=sys.stderr)

    print(f"""import StripSearch

namespace Grid75.StripSearch

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

/- Every consecutive band of {width} original rows has a verified refutation. -/
refute_strips certificates {width} {SIDE - width}

end Grid75.StripSearch""")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("Usage: python search_windows.py WIDTH")
    try:
        run(int(sys.argv[1]))
    except Found as found:
        ps = found.args[0]
        print("import Grid75\nnamespace Grid75\ndef candidate : List Point := [")
        print(", ".join(f"({x}, {y})" for x, y in map(coords, ps)) + "]")
        print("set_option maxRecDepth 10000 in\nset_option maxHeartbeats 0 in")
        print("theorem found150 : Achievable 150 := by")
        print("  have nd : candidate.Nodup := by decide +kernel")
        print("  exact ⟨candidate, by decide, nd, slopes_sound nd (by decide +kernel)⟩")
        print("end Grid75")
