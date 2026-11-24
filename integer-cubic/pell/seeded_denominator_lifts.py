"""Test denominator rescalings of cubic Pell graphs at 7, for D = 3.

Run with: uv run --with python-flint==0.9.0 seeded_denominator_lifts.py

At a maximal positive slope h the balanced chart has Q = 1−3·7^(2h)t².
Its three integer-polynomial representatives have degree at most six and
their constants are the prescribed seed. The residue search below also
checks that every admissible slope is an integer. Each successful
correction admits 7^(18-rank) next digits. Counts at a given modulus
therefore refer to distinct coefficient triples at that modulus.
"""

from collections import Counter
from itertools import product
from math import gcd
from pathlib import Path

from flint import fmpz_poly, nmod_mat

from search_pell_mod import cubic_candidates


PRIME = 7
T = fmpz_poly([0, 1])
SEEDS = ((0, 1, 1), (-2, 3, 1))


def residual(triple, q):
    """The coefficients of this polynomial must vanish at every precision."""
    x, y, z = triple
    return x**3 + z*y**2 + z**2*q**3 - 2*q**9


def correction_rhs(error, modulus):
    assert error[0] == 0 and error.degree() <= 18
    assert all(int(value) % modulus == 0 for value in error.coeffs())
    return [(-int(error[i]) // modulus) % PRIME for i in range(1, 19)]


class CorrectionSystem:
    def __init__(self, triple):
        x, y, z = triple
        # Q reduces to 1. The constants are fixed, leaving eighteen columns.
        derivatives = (3*x**2, 2*y*z, y**2 + 2*z)
        columns = [p*T**i for p in derivatives for i in range(1, 7)]
        self.rows = [[int(p[i]) % PRIME for p in columns] for i in range(1, 19)]
        matrix = nmod_mat(self.rows, PRIME)
        self.rank = matrix.rank()
        augmented = [row + [int(i == j) for j in range(18)]
                     for i, row in enumerate(self.rows)]
        echelon, _ = nmod_mat(augmented, PRIME).rref()
        rows = [[int(a) for a in row] for row in echelon.tolist()[:self.rank]]
        self.solver = [(next(i for i, a in enumerate(row[:18]) if a), row[18:])
                       for row in rows]
        basis, dimension = matrix.nullspace()
        self.directions = [
            tuple(fmpz_poly([0, *[int(basis[start+i, j]) for i in range(6)]])
                  for start in (0, 6, 12)) for j in range(dimension)
        ]
        kernel, dimension = matrix.transpose().nullspace()
        self.left_kernel = [
            [int(kernel[i, j]) for i in range(18)] for j in range(dimension)
        ]
        assert dimension == 18 - self.rank

    def solvable(self, rhs):
        return not any(self.projection(rhs))

    def projection(self, rhs):
        return [sum(a*b for a, b in zip(row, rhs)) % PRIME for row in self.left_kernel]

    def particular(self, rhs):
        digits = [0]*18
        for pivot, row in self.solver:
            digits[pivot] = sum(a*b for a, b in zip(row, rhs)) % PRIME
        return digits

    def solutions(self, rhs):
        augmented = nmod_mat([row + [b] for row, b in zip(self.rows, rhs)], PRIME)
        reduced, rank = augmented.rref()
        assert (rank == self.rank) == self.solvable(rhs)
        if rank != self.rank:
            return
        rows = [[int(a) for a in row] for row in reduced.tolist()[:rank]]
        pivots = [next(i for i, a in enumerate(row) if a) for row in rows]
        free = [i for i in range(18) if i not in pivots]
        for parameters in product(range(PRIME), repeat=len(free)):
            digits = [0]*18
            for i, a in zip(free, parameters):
                digits[i] = a
            for i, row in zip(pivots, rows):
                digits[i] = (row[18] - sum(row[j]*digits[j] for j in free)) % PRIME
            yield digits


def add_digits(triple, digits, modulus):
    return tuple(f + modulus*fmpz_poly([0, *digits[j:j+6]])
                 for f, j in zip(triple, (0, 6, 12)))


def third_digit_projection(system, candidate):
    """Variation of the third-digit obstruction as a second digit runs over ker J."""
    x, y, z = candidate
    columns = []
    for dx, dy, dz in system.directions:
        # For all h, Q=1 mod 49, sufficient after dividing this derivative by 7.
        derivative = 3*x**2*dx + 2*y*z*dy + (y**2+2*z)*dz
        assert all(int(c) % PRIME == 0 for c in derivative.coeffs())
        next_digit = [int(derivative[i]//PRIME) % PRIME for i in range(1, 19)]
        columns.append(system.projection(next_digit))
    return [list(row) for row in zip(*columns)]


def verify_lean_certificate(excluded):
    """Match the exceptional orbit, the Jacobian rows and the first digits to Lean."""
    representative = ((-2, 1, 2, 1, 5), (3, 2, 5, 3), (1, 1, 3, 4, 2, 2, 2))
    def scaled_residue(scale):
        return tuple(tuple(a*scale**i % PRIME for i, a in enumerate(row))
                     for row in representative)
    assert excluded == {scaled_residue(u) for u in range(1, PRIME)}

    base = tuple(fmpz_poly(list(row)) for row in representative)
    system = CorrectionSystem(base)
    lean = Path(__file__).with_name("SeedDenominatorObstruction.lean").read_text()
    def lean_list(row):
        return "[" + ",".join(map(str, row)) + "]"
    for name, row in zip("xyz", representative):
        assert f"private def {name} : List ℤ := {lean_list(row)}" in lean
    rhs = correction_rhs(residual(base, 1), PRIME)
    for label, index, forced in zip(("0", "1", "_"), (5, 10, 11), (6, 1, 0)):
        row = dict(system.solver)[index].copy()
        assert [sum(a*b for a, b in zip(row, col)) % PRIME
                for col in zip(*system.rows)] == [int(j == index) for j in range(18)]
        assert sum(a*b for a, b in zip(row, rhs)) % PRIME == forced
        while row and row[-1] == 0:
            row.pop()
        assert f"| {label} => {lean_list(row)}" in lean
    # Check the coefficient formula against the full residual for every
    # choice of the three free digits and every denominator modulo 343.
    for digits in system.solutions(rhs):
        lifted = add_digits(base, digits, PRIME)
        for c in range(PRIME):
            q = 1 + PRIME**2*c*T**2
            assert int(residual(lifted, q)[16]) % PRIME**3 == 3*PRIME**2


def check_seed(seed):
    # D=0 here means Q=1 in the residue calculation, for every positive h.
    distribution = Counter()
    excluded = set()
    for polynomials in cubic_candidates(PRIME, 0, seed):
        support = [i for p in polynomials for i in range(1, 7) if int(p[i])]
        if not support:
            continue
        # If h=a/b in lowest terms and ord_7(a_i)+i*h=0, then b divides i.
        # The original coefficients lie in Q_7. We can balance in a totally
        # ramified extension with 7^(1/b), retaining residue field F_7.
        assert gcd(*support) == 1
        base = tuple(fmpz_poly([v, *map(int, f.coeffs()[1:])])
                     for v, f in zip(seed, polynomials))
        system = CorrectionSystem(base)
        totals = [0, 0, 0, 0, 0]
        for digits in system.solutions(correction_rhs(residual(base, 1), PRIME)):
            candidate = add_digits(base, digits, PRIME)
            totals[0] += 1
            projected = None
            for j, q in enumerate((1 - 3*PRIME**2*T**2, 1), 1):
                # For h>=2 the exact Q agrees with 1 even modulo 7^4.
                rhs = correction_rhs(residual(candidate, q), PRIME**2)
                if system.solvable(rhs):
                    totals[j] += 1
                    # Every mod-343 lift of candidate is a particular lift plus
                    # 49 times a linear combination of the kernel directions.
                    # Terms quadratic in 49 vanish mod 2401. Projecting away
                    # im J gives a three-variable linear system, which counts
                    # the lifts that continue without enumerating them all.
                    if projected is None:
                        projected = third_digit_projection(system, candidate)
                        rank = nmod_mat(projected, PRIME).rank()
                    particular = add_digits(candidate, system.particular(rhs), PRIME**2)
                    next_error = residual(particular, q)
                    next_rhs = system.projection(correction_rhs(next_error, PRIME**3))
                    matrix = [row+[digit] for row, digit in zip(projected, next_rhs)]
                    if nmod_mat(matrix, PRIME).rank() == rank:
                        totals[2+j] += PRIME**(len(system.directions)-rank)
        distribution[(system.rank, *totals)] += 1
        if totals[1] == totals[2] == 0:
            excluded.add(tuple(tuple(map(int, f.coeffs())) for f in polynomials))
    if seed == SEEDS[1]:
        verify_lean_certificate(excluded)
    print(f"seed {seed}: {sum(distribution.values())} nonconstant residues")
    for counts, count in sorted(distribution.items()):
        rank, count49, count343_h1, count343_h2, count2401_h1, count2401_h2 = counts
        print(f"  {count} residues of rank {rank}: {count49} lifts modulo 49 each; "
              f"{count343_h1} lift further for h=1, {count343_h2} for h>=2; "
              f"mod-343 lifts extending to 2401: {count2401_h1} for h=1, {count2401_h2} for h>=2")
    return distribution


if __name__ == "__main__":
    first, second = (check_seed(seed) for seed in SEEDS)
    assert first == {(15, 343, 343, 343, 117649, 117649): 6}
    assert second == {
        (15, 343, 0, 0, 0, 0): 6,
        (15, 343, 343, 343, 16807, 16807): 24,
        (15, 343, 343, 343, 117649, 117649): 12,
    }
