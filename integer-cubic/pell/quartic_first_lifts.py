"""Lift mixed quartic Pell candidates at (0,1,1), D=3, through modulus 343.

Run: uv run --with python-flint==0.9.0 quartic_first_lifts.py
Use --orbits FILE with the JSON-lines output of search_quartic_pell.py.
Coordinates X,Y,Z have degrees at most 8,6,12, with constant terms 0,1,1.
"""

import argparse
import json
from itertools import combinations, product
from pathlib import Path

from flint import fmpz_poly, nmod_mat

P = 7
T = fmpz_poly([0, 1])
TARGET = 2*(1-3*T**2)**12
DEGREES = (8, 6, 12)
PILOT = ((0, 0, 0, 0, 3), (1, 0, 5, 3, 6, 0, 1),
         (1, 0, 3, 5, 2, 4, 1, 2, 4, 5, 5, 0, 1))


def residual(triple):
    x, y, z = triple
    return x**3 + z*y**2 + z**2 - TARGET


def rhs(triple, modulus):
    r = residual(triple)
    assert r.degree() <= 24 and r[0] == 0
    coefficients = [int(r[i]) for i in range(1, 25)]
    assert all(c % modulus == 0 for c in coefficients)
    return [-c//modulus % P for c in coefficients]


def poly_triple(digits):
    return tuple(fmpz_poly([0, *digits[i:j]]) for i, j in ((0, 8), (8, 14), (14, 26)))


def translate(triple, multiplier, direction):
    return tuple(f + multiplier*g for f, g in zip(triple, direction))


def kernel(matrix):
    basis, dimension = matrix.nullspace()
    return [tuple(int(basis[i, j]) for i in range(matrix.ncols())) for j in range(dimension)]


class QuarticLifts:
    def __init__(self, base):
        base = tuple(fmpz_poly(list(row)) for row in base)
        x, y, z = base
        assert (x[0], y[0], z[0]) == (0, 1, 1)
        derivatives = (3*x*x, 2*y*z, y*y + 2*z)
        columns = [f*T**i for f, degree in zip(derivatives, DEGREES) for i in range(1, degree+1)]
        self.matrix = nmod_mat([[int(c[i]) for c in columns] for i in range(1, 25)], P)
        matrix = self.matrix
        self.rank = matrix.rank()
        # RREF of [M | I] carries along the row operations for solving M w = rhs.
        echelon, _ = nmod_mat([row + [int(i == j) for j in range(24)]
                                for i, row in enumerate(matrix.tolist())], P).rref()
        rows = [list(map(int, row)) for row in echelon.tolist()[:self.rank]]
        self.solver = [(next(i for i, a in enumerate(row[:26]) if a), row[26:]) for row in rows]
        self.left = kernel(matrix.transpose())
        self.directions = [poly_triple(d) for d in kernel(matrix)]
        self.pairs = list(combinations(range(len(self.directions)), 2))
        first = rhs(base, P)
        assert not any(self.project(first))
        self.first = translate(base, P, self.particular(first))
        self.forms = self.quadratic_forms()

    def particular(self, values):
        digits = [0]*26
        for pivot, row in self.solver:
            digits[pivot] = sum(a*b for a, b in zip(row, values)) % P
        return poly_triple(digits)

    def project(self, values):
        return tuple(sum(a*b for a, b in zip(row, values)) % P for row in self.left)

    def sample(self, terms):
        triple = self.first
        for scalar, direction in terms:
            triple = translate(triple, P*scalar, self.directions[direction])
        return self.project(rhs(triple, P**2))

    def quadratic_forms(self):
        # For F the cubic residual and h any integer combination of kernel vectors,
        # F(first+7h)/49 = F(first)/49 + dF(first)h/7 + Q(first,h) mod 7.
        # The cubic homogeneous part in h has an extra factor 7. Thus values at
        # 0, ±e_i and e_i+e_j determine every projected obstruction exactly.
        const = self.sample([])
        lin, sq, mixed = [], [], []
        for i in range(len(self.directions)):
            plus = self.sample([(1, i)])
            minus = self.sample([(-1, i)])
            lin.append(tuple(4*(a-b) % P for a, b in zip(plus, minus)))
            sq.append(tuple((4*(a+b)-c) % P for a, b, c in zip(plus, minus, const)))
        for i, j in self.pairs:
            plus = self.sample([(1, i), (1, j)])
            mixed.append(tuple((a-b-c-d-e-f) % P
                               for a,b,c,d,e,f in zip(plus, lin[i], lin[j], sq[i], sq[j], const)))
        return nmod_mat([const, *lin, *sq, *mixed], P) if self.left else None

    def monomials(self, u):
        return [1, *u, *(x*x for x in u), *(u[i]*u[j] for i,j in self.pairs)]

    def surviving_digits(self):
        dimension = len(self.directions)
        if self.forms is None:
            yield from product(range(P), repeat=dimension)
            return
        for first in range(P):
            batch = [(first, *v) for v in product(range(P), repeat=dimension-1)]
            evaluation = nmod_mat([self.monomials(v) for v in batch], P)*self.forms
            for digits, values in zip(batch, evaluation.tolist()):
                if not any(values):
                    yield digits

    def obstruction_rank(self, digits):
        if self.forms is None:
            return 0
        # For quadratics in odd characteristic, the centered first difference
        # at ±1 is twice the formal derivative in that coordinate.
        differences = []
        for j in range(len(digits)):
            plus, minus = list(digits), list(digits)
            plus[j] += 1
            minus[j] -= 1
            differences.append([4*(p-m) for p,m in zip(self.monomials(plus), self.monomials(minus))])
        return (nmod_mat(differences, P)*self.forms).rank()

    def verify_lift(self, digits):
        candidate = self.first
        for i, v in enumerate(digits):
            candidate = translate(candidate, P*v, self.directions[i])
        values = rhs(candidate, P**2)
        assert not any(self.project(values))
        lifted = translate(candidate, P**2, self.particular(values))
        rhs(lifted, P**3)  # Check all 24 coefficients directly modulo 343.


def check_pilot_certificate(system, survivors):
    reduced, rank = system.forms.transpose().rref()
    assert rank == 4
    rows = [list(map(int, row)) for row in reduced.tolist()]
    lean = Path(__file__).with_name("QuarticLift.lean").read_text()
    for i, row in enumerate(rows):
        label = str(i) if i < 3 else "_"
        assert f"| {label} => {row}" in lean
    # This is the bijection in QuarticLift.pilot_digits_iff (coordinates ordered
    # by the free columns of the FLINT nullspace). Check it on the actual results.
    expected = {((-c-2*d-4*s-3) % P, (-d-3*s-4) % P, c, d, 0, s)
                for c, d, s in product(range(P), range(P), (1, 6))}
    assert survivors == expected


def analyze(base, pilot=False):
    system = QuarticLifts(base)
    surviving = set(system.surviving_digits())
    for digits in surviving:
        system.verify_lift(digits)
        assert system.obstruction_rank(digits) == len(system.left)
    if pilot:
        check_pilot_certificate(system, surviving)
    return system.rank, len(surviving), P**len(system.directions)


def pilot_orbit():
    for scalar, sign in product((1, 2, 4), (1, -1)):
        yield tuple(tuple(a*sign**i*(scalar if j == 0 else 1) % P
                          for i, a in enumerate(row)) for j, row in enumerate(PILOT))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orbits", help="also lift representatives from search_quartic_pell.py")
    args = parser.parse_args()
    for i, base in enumerate(pilot_orbit()):
        rank, count, multiplicity = analyze(base, pilot=i==0)
        assert (rank, count, multiplicity) == (20, 98, 117649)
    print("Pilot: all six residues have 117649 first lifts; 98 each extend,")
    print("with 117649 second corrections each, giving 69177612 triples modulo 343.")
    if args.orbits:
        with open(args.orbits) as records:
            for line in records:
                branch = json.loads(line)
                rank, count, multiplicity = analyze(tuple(branch[k] for k in "xyz"))
                assert rank == branch["rank"]
                print(f"x={branch['x']} y={branch['y']} orbit={branch['orbit']}: "
                      f"{count}/{multiplicity} modulo-49 triples extend, "
                      f"{count*multiplicity} lifts modulo 343 per residue")


if __name__ == "__main__":
    main()
