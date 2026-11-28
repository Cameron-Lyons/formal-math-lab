"""Construct the cubic coloring in the README and check every cyclic progression."""

import argparse
from collections import defaultdict
from itertools import combinations, count, product
from math import isqrt


def digit_tag(x, modulus):
    distance = 1 + 2 * min(x, modulus - 1 - x)
    return (x % 2, 2 * x < modulus, (distance.bit_length() - 1) % 3)


def interval_auxiliary(x, base, digits):
    tags = []
    norm = 0
    for _ in range(digits):
        x, digit = divmod(x, base)
        parity, lower, band = digit_tag(digit, base)
        if not lower:
            tags.append(4 + 3 * parity + band)
        elif 3 * (2 * digit + 1) < 2 * base:
            tags.append(band)
        else:
            tags.append(3)
        norm += digit**2
    return tuple(tags), norm


def multiplicative_colors(p):
    colors = [0] * p
    ratios = {r % p for r in (-1, 4, 3, -3)}
    ratios |= {pow(r, -1, p) for r in ratios}
    for x in range(1, p):
        neighbors = {r * x % p for r in ratios}
        used = {colors[y] for y in neighbors if y < x}
        colors[x] = next(c for c in range(8) if c not in used)
    return colors


def cubic_coloring(p, base):
    # A cubic over a field is irreducible exactly when it has no root.
    a, b = next(
        (a, b)
        for a, b in product(range(p), repeat=2)
        if all((t**3 + a * t + b) % p for t in range(p))
    )
    digits = next(k for k in count(1) if base**k >= p**2)
    auxiliary = [
        (digit_tag(x, p**2), interval_auxiliary(x, base, digits)) for x in range(p**2)
    ]
    graph = multiplicative_colors(p)
    shift = -2 * a * pow(3, -1, p)
    tags = [digit_tag(x, p) for x in range(p)]
    colors = []
    palette = {}
    for n in range(p**4):
        high, low = divmod(n, p**2)
        z, y = divmod(high, p)
        x1, x0 = divmod(low, p)
        # Norm(y+x0*t+x1*t²) is the determinant of multiplication
        # by this element in the basis (1,t,t²), where t³ = -a*t-b.
        diag = y - a * x1
        off = -a * x0 - b * x1
        norm = (
            y * (diag**2 - off * x0)
            + b * x1 * (x0 * diag - off * x1)
            - b * x0 * (x0**2 - diag * x1)
        )
        color = (
            tags[x0],
            tags[x1],
            tags[y],
            (norm + z) % p,
            auxiliary[low],
            graph[(y + shift * x1) % p],
        )
        colors.append(palette.setdefault(color, len(palette)))
    return colors


def verify(colors):
    n = len(colors)
    classes = defaultdict(list)
    for x, color in enumerate(colors):
        classes[color].append(x)
    placements = [(i, pow(j - i, -1, n)) for i, j in combinations(range(4), 2)]
    checked = 0
    # Every failure has a repeated pair x,y. Orient the progression so x<y,
    # place this pair at i<j, and recover its unique step modulo p^4.
    for positions in classes.values():
        for x, y in combinations(positions, 2):
            for i, inverse_gap in placements:
                step = (y - x) * inverse_gap % n
                start = (x - i * step) % n
                if len({colors[(start + k * step) % n] for k in range(4)}) < 3:
                    raise ValueError(f"failed at start {start}, step {step}")
                checked += 1
    return checked


def verify_cubic_slices(p):
    graph = multiplicative_colors(p)
    repaired = 0
    # Up to scaling and translation of the output, every cubic in the last
    # two digits with nonzero y-step has F_i=(t+i)^3+s*i and u_i=(t+i)*b.
    for t, slope in product(range(p), repeat=2):
        values = [((t + i) ** 3 + slope * i) % p for i in range(4)]
        if len(set(values)) >= 3:
            continue
        for b in range(1, p):
            tag = [graph[(t + i) * b % p] for i in range(4)]
            if len(set(zip(values, tag, strict=True))) < 3:
                raise ValueError(f"cubic graph failed at t={t}, slope={slope}, b={b}")
            repaired += 1
    return repaired


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, default=19, help="prime greater than five")
    parser.add_argument("--base", type=int, default=5, help="odd auxiliary radix")
    args = parser.parse_args()
    p = args.prime
    if p <= 5 or any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        parser.error("--prime must be a prime greater than five")
    if args.base < 3 or args.base % 2 == 0:
        parser.error("--base must be an odd integer at least three")
    repaired = verify_cubic_slices(p)
    coloring = cubic_coloring(p, args.base)
    checked = verify(coloring)
    print(
        f"modulus {p**4}, {len(set(coloring))} colors, "
        f"{checked} repeated-pair placements, all valid; "
        f"graph tag repairs {repaired} normalized cubic cases"
    )
