"""Count the size-k zero-sum sets tested by the cycle verifier at 41 or 43.

Print the number of zero-sum sets, their multiplicative orbits, and the
number of words with nonnegative prefix heights (the C++ search cases).
A single orbit can contribute several different words in the last column.
An optional C++ transcript must give one "size count" row for every size
from 2 through p−3.
"""

import argparse
from collections import Counter
from fractions import Fraction
from math import comb, gcd
from pathlib import Path

GENERATORS = {41: 6, 43: 3}


def count_by_returns(size: int, powers: tuple[int, ...]) -> Counter[int]:
    """Count admissible words by their number of returns to height zero."""
    length = len(powers)
    prime = length + 1
    # After j steps with c chosen residues, the height is j*size - length*c.
    # Each state holds the number of prefixes with the indicated selection
    # count, selected sum modulo p, and number of returns so far.
    prefixes = Counter({(0, 0, 0): 1})
    for j, value in enumerate(powers, start=1):
        following: Counter[tuple[int, int, int]] = Counter()
        for (chosen, residue, returns), ways in prefixes.items():
            for take in (0, 1):
                count = chosen + take
                height = j * size - length * count
                if height < 0 or count + length - j < size:
                    continue
                new_sum = (residue + take * value) % prime
                following[count, new_sum, returns + (height == 0)] += ways
        prefixes = following
    return Counter(
        {r: ways for (c, s, r), ways in prefixes.items() if c == size and s == 0}
    )


def zero_sets(size: int, prime: int) -> int:
    # Average the generating polynomials over the p additive characters.
    # The trivial character gives (1+x)^(p−1). For each other character the
    # product over nonzero residues is (1+x^p)/(1+x), with coefficient (-1)^k.
    length = prime - 1
    sign = 1 if size % 2 == 0 else -1
    return (comb(length, size) + length * sign) // prime


def dilation_orbits(size: int, raw: int, length: int) -> int:
    # In Burnside's formula, the i-th power of the generator has cycles
    # of length d, each of sum zero for d>1. A fixed set uses whole cycles.
    fixed_sum = raw
    for i in range(1, length):
        order = length // gcd(i, length)
        if size % order == 0:
            fixed_sum += comb(length // order, size // order)
    orbits, remainder = divmod(fixed_sum, length)
    if remainder:
        raise ValueError(f"nonintegral orbit count at size {size}")
    return orbits


def read_transcript(path: Path, prime: int) -> dict[int, int]:
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
    expected = set(range(2, prime - 2))
    if result.keys() != expected:
        raise ValueError(
            f"missing sizes {sorted(expected - result.keys())}; "
            f"unexpected sizes {sorted(result.keys() - expected)}"
        )
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("transcript", type=Path, nargs="?")
    parser.add_argument("--prime", type=int, choices=GENERATORS, default=41)
    args = parser.parse_args()
    prime = args.prime
    length = prime - 1
    generator = GENERATORS[prime]
    powers = tuple(pow(generator, i, prime) for i in range(length))
    observed = (
        read_transcript(args.transcript, prime) if args.transcript is not None else {}
    )
    if set(powers) != set(range(1, prime)):
        raise ValueError(
            f"{generator} must generate the nonzero residues modulo {prime}"
        )
    print("size\tzero_sum_sets\tdilation_orbits\tnonnegative_words")
    for size in range(length + 1):
        by_returns = count_by_returns(size, powers)
        raw = zero_sets(size, prime)
        # A nonnegative word returning r times admits r nonnegative cuts
        # among its p−1 labelled cuts. Each word represents (p−1)/r raw
        # words in this weighted count, even if its rotation orbit is short.
        weighted = sum(Fraction(length * ways, r) for r, ways in by_returns.items())
        if weighted != raw:
            raise ValueError(f"coverage mismatch at size {size}: {weighted} != {raw}")
        words = by_returns.total()
        if size in observed and observed[size] != words:
            raise ValueError(
                f"size {size}: C++ counted {observed[size]}, expected {words}"
            )
        print(size, raw, dilation_orbits(size, raw, length), words, sep="\t")
    if observed:
        print(f"All {len(observed)} transcript counts match.")


if __name__ == "__main__":
    main()
