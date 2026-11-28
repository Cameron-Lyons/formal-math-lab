"""Run from the repository root with python3 research/erdos-311/verify_grid.py."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt, prod


@dataclass(frozen=True)
class Grid:
    """Represents m / denominator for every integer first <= m <= denominator."""

    denominator: int
    first: int
    bound: int
    previous: Grid | None = None
    primes: tuple[int, ...] = ()

    def lift(self, primes: tuple[int, ...]) -> Grid:
        """Attach disjoint copies of the old denominators, one per prime."""
        assert primes and len(set(primes)) == len(primes)
        for p in primes:
            assert p >= 2 and all(p % j != 0 for j in range(2, isqrt(p) + 1))
            assert self.denominator % p != 0
            assert p <= self.denominator - self.first + 1

        product = prod(primes)
        denominator = self.denominator * product
        # Increase the old lower endpoint by the sum of the reciprocal primes.
        first = self.first * product + self.denominator * sum(
            product // p for p in primes
        )
        assert first <= denominator
        return Grid(denominator, first, self.bound * max(primes), self, primes)

    def represent(self, numerator: int) -> list[int]:
        assert self.first <= numerator <= self.denominator
        old = self.previous
        if old is None:
            # Each binary digit 2^k of m contributes 1 / (D / 2^k).
            assert self.denominator > 0 and self.denominator.bit_count() == 1
            return [
                self.denominator >> k
                for k in range(numerator.bit_length())
                if numerator & (1 << k)
            ]

        product = self.denominator // old.denominator
        remainder = numerator
        terms = []
        for p in self.primes:
            cofactor = product // p
            residue = numerator * pow(cofactor, -1, p) % p
            block = old.first + (residue - old.first) % p
            # The p-scaled copy contributes block / (p * old.denominator).
            terms.extend(p * n for n in old.represent(block))
            remainder -= block * cofactor

        old_numerator, residue = divmod(remainder, product)
        assert residue == 0
        terms.extend(old.represent(old_numerator))
        return terms


def verify(grid: Grid, numerator: int) -> list[int]:
    """Check the returned denominators and sum directly using rational arithmetic."""
    terms = grid.represent(numerator)
    assert len(terms) == len(set(terms))
    assert all(1 <= n <= grid.bound and grid.denominator % n == 0 for n in terms)
    assert sum(Fraction(1, n) for n in terms) == Fraction(numerator, grid.denominator)
    return sorted(terms)


def main() -> None:
    base = Grid(denominator=16, first=8, bound=16)
    first = base.lift((5, 7))
    for grid in (base, first):
        for numerator in range(grid.first, grid.denominator + 1):
            verify(grid, numerator)
        count = grid.denominator - grid.first + 1
        print(
            f"D={grid.denominator} verified all {count} numerators {grid.first}..{grid.denominator}"
        )

    second = first.lift((23, 29))
    for numerator in (second.first, second.denominator - 1, second.denominator):
        terms = verify(second, numerator)
        print(
            f"{Fraction(numerator, second.denominator)} = "
            + " + ".join(f"1/{n}" for n in terms)
        )
    print(
        f"Two lifts give 1 - 1/{second.denominator} with denominators at most {second.bound}."
    )


if __name__ == "__main__":
    main()
