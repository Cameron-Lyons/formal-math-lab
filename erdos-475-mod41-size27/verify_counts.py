"""Count the size-k zero-sum sets tested by the modulo-41 cycle verifier.

Print the number of zero-sum sets, their multiplicative orbits, and the
number of words with nonnegative prefix heights (the C++ search cases).
A single orbit can contribute several different words in the last column.
An optional C++ transcript must give one "size count" row for every size 2–38.
"""

import argparse
from collections import Counter
from fractions import Fraction
from math import comb, gcd
from pathlib import Path

PRIME = 41
LENGTH = PRIME - 1
POWERS = tuple(pow(6, i, PRIME) for i in range(LENGTH))


def count_by_returns(size: int) -> Counter[int]:
    """Count admissible words by their number of returns to height zero."""
    # After j steps with c chosen residues, the height is j*size - 40*c.
    # Each state holds the number of prefixes with the indicated selection
    # count, selected sum modulo 41, and number of returns so far.
    prefixes = Counter({(0, 0, 0): 1})
    for j, value in enumerate(POWERS, start=1):
        following: Counter[tuple[int, int, int]] = Counter()
        for (chosen, residue, returns), ways in prefixes.items():
            for take in (0, 1):
                count = chosen + take
                height = j * size - LENGTH * count
                if height < 0 or count + LENGTH - j < size:
                    continue
                new_sum = (residue + take * value) % PRIME
                following[count, new_sum, returns + (height == 0)] += ways
        prefixes = following
    return Counter(
        {r: ways for (c, s, r), ways in prefixes.items() if c == size and s == 0}
    )


def zero_sets(size: int) -> int:
    # Average the generating polynomials over the 41 additive characters.
    # The trivial character gives (1+x)^40. For each other character the
    # product over the 40 residues is (1+x^41)/(1+x), with coefficient (-1)^k.
    sign = 1 if size % 2 == 0 else -1
    return (comb(LENGTH, size) + LENGTH * sign) // PRIME


def dilation_orbits(size: int, raw: int) -> int:
    # Burnside: multiplication by 6^i has cycles of length d, each of sum
    # zero when d>1. A fixed set is a union of whole cycles.
    fixed_sum = raw
    for i in range(1, LENGTH):
        order = LENGTH // gcd(i, LENGTH)
        if size % order == 0:
            fixed_sum += comb(LENGTH // order, size // order)
    orbits, remainder = divmod(fixed_sum, LENGTH)
    if remainder:
        raise ValueError(f"nonintegral orbit count at size {size}")
    return orbits


def read_transcript(path: Path) -> dict[int, int]:
    result: dict[int, int] = {}
    for line in path.read_text().splitlines():
        fields = line.split()
        if not fields or not fields[0].isdecimal():
            continue
        if len(fields) != 2 or not fields[1].isdecimal():
            raise ValueError(f"malformed size/count row: {line!r}")
        size, count = map(int, fields)
        if size in result:
            raise ValueError(f"duplicate transcript row for size {size}")
        result[size] = count
    expected = set(range(2, 39))
    if result.keys() != expected:
        raise ValueError(
            f"missing sizes {sorted(expected - result.keys())}; "
            f"unexpected sizes {sorted(result.keys() - expected)}"
        )
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("transcript", type=Path, nargs="?")
    args = parser.parse_args()
    observed = read_transcript(args.transcript) if args.transcript is not None else {}
    if set(POWERS) != set(range(1, PRIME)):
        raise ValueError("6 must generate the nonzero residues")
    print("size\tzero_sum_sets\tdilation_orbits\tnonnegative_words")
    for size in range(LENGTH + 1):
        by_returns = count_by_returns(size)
        raw = zero_sets(size)
        # A nonnegative word returning r times admits r nonnegative cuts
        # among its 40 labelled cuts. Each such word represents 40/r raw
        # words in this weighted count, even if its rotation orbit is short.
        weighted = sum(Fraction(LENGTH * ways, r) for r, ways in by_returns.items())
        if weighted != raw:
            raise ValueError(f"coverage mismatch at size {size}: {weighted} != {raw}")
        words = by_returns.total()
        if size in observed and observed[size] != words:
            raise ValueError(
                f"size {size}: C++ counted {observed[size]}, expected {words}"
            )
        print(size, raw, dilation_orbits(size, raw), words, sep="\t")
    if observed:
        print("All 37 transcript counts match.")


if __name__ == "__main__":
    main()
