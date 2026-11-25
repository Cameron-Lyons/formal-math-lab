"""Exhaust the balanced mod-7 cubic residues and verify the uniform local obstruction applies.

Run with uv run --with python-flint==0.9.0 cubic_annulus_residues.py.
"""

from collections import Counter
from math import gcd

from search_pell_mod import cubic_candidates
from seeded_denominator_lifts import SEEDS


def main():
    seeds = (*SEEDS, (1, 0, 1), (1, 0, -1))
    for seed, expected in zip(seeds, (6, 42, 18, 18), strict=False):
        degrees = Counter()
        for x, y, z in cubic_candidates(7, 0, seed):
            support = [j for f in (x, y, z) for j in range(1, 7) if f[j]]
            if not support:
                continue
            assert gcd(*support) == 1
            degrees[y.degree(), z.degree()] += 1
        assert degrees == {(3, 6): expected}
        print(
            f"{seed}: {expected} nonconstant triples, all with (deg Y, deg Z) = (3, 6)"
        )


if __name__ == "__main__":
    main()
