"""The primary two-mark quartic Pell problem at 2, for every positive balancing slope.

Run with uv run --with python-flint==0.9.0 python two_point_primary_two.py.
The original-lattice case is checked in quartic_local_geometry.py.
"""
from ast import literal_eval
from fractions import Fraction
from itertools import product
from pathlib import Path

from flint import fmpz_poly, nmod_mat


DEGREES = (4, 3, 6)
# (constant of P, constant of Q) so P(0) and P(0)+Q(0) are the marked coordinates.
MARKS = ((0, 1), (1, -1), (1, -2))
INDICES = [(j, m, i) for j, d in enumerate(DEGREES)
           for m in range(2) for i in range(1, d + 1 - m)]
OUTPUT = [(m, i) for m in range(2) for i in range(1, 13 - m)]
T = fmpz_poly([0, 1])
ZERO = fmpz_poly([])
ONE = fmpz_poly([1])


def binary_product(f, g):
    """Multiply bit-polynomials in F₂[s]."""
    result = 0
    while g:
        if g & 1:
            result ^= f
        f <<= 1
        g >>= 1
    return result


def ordinary(mark):
    """All bounded-degree polynomial solutions through a specified point over F₂."""
    triples = []
    for x, y, z in product(*(range(c, 1 << (d + 1), 2) for c, d in zip(mark, DEGREES))):
        if binary_product(z, z ^ binary_product(y, y)) == binary_product(x, binary_product(x, x)):
            triples.append((x, y, z))
    return triples


def split_residues(denominator, target=(1, 0, 1)):
    """The two v=0,1 components must differ by Q of degree strictly below d."""
    rows = []
    for a, b in product(ordinary((0, 1, 1)), ordinary(target)):
        q = tuple(x ^ y for x, y in zip(a, b))
        if any(g >> d for g, d in zip(q, DEGREES)):
            continue
        if any(g >> i & 1 for g in (*a, *q) for i in range(g.bit_length()) if i % denominator):
            continue
        if any(g > 1 for g in (*a, *q)):  # Some positive index attains the balancing slope.
            rows.append((a, q))
    return rows


class SlopeChart:
    """Integer arithmetic in the basis w^i / 2^floor(h*i), with v degree at most one."""

    def __init__(self, slope, marks=MARKS):
        self.marks = marks
        # At w=0, the scalar and v coefficients interpolate the two marked errors.
        def error(point):
            x, y, z = point
            return x**3 + y*y*z + z*z - 2

        first = error(tuple(p for p, _ in marks))
        second = error(tuple(p+q for p, q in marks))
        self.constant_error = (first, second-first)
        self.slope = slope
        # Substitute w=2^b s. Divide each output coefficient by the same basis factor
        # to recover its coefficient in the normalized lattice, before reducing it.
        b = -(-slope.numerator // slope.denominator)
        r = 2**b
        self.factor = [2**(b*i - int(slope*i)) for i in range(13)]
        self.v_square = (r*T + r*r//2*T*T, ONE + r*T)
        self.columns = [(self.factor[i]*T**i, ZERO) if m == 0
                        else (ZERO, self.factor[i]*T**i) for _, m, i in INDICES]

    def multiply(self, p, q):
        c, d = self.v_square
        mixed = p[1]*q[1]
        return (p[0]*q[0] + mixed*c, p[1]*q[0] + p[0]*q[1] + mixed*d)

    def coordinates(self, coefficients):
        coords = [[ONE*a, ONE*b] for a, b in self.marks]
        for value, (j, m, i) in zip(coefficients, INDICES):
            if value:
                coords[j][m] += value*self.factor[i]*T**i
        return coords

    def identity(self, coefficients):
        x, y, z = self.coordinates(coefficients)
        x3 = self.multiply(x, self.multiply(x, x))
        y2z = self.multiply(z, self.multiply(y, y))
        z2 = self.multiply(z, z)
        result = (x3[0]+y2z[0]+z2[0]-2, x3[1]+y2z[1]+z2[1])
        assert tuple(int(p[0]) for p in result) == self.constant_error
        assert result[0].degree() <= 12 and result[1].degree() <= 11
        return result

    def digit(self, pair, level):
        values = []
        for m, i in OUTPUT:
            q, remainder = divmod(int(pair[m][i]), self.factor[i] * 2**level)
            assert remainder == 0
            values.append(q % 2)
        return values

    def correction_matrix(self, coefficients):
        x, y, z = self.coordinates(coefficients)
        x2, yz, y2 = self.multiply(x, x), self.multiply(y, z), self.multiply(y, y)
        derivatives = (tuple(3*f for f in x2), tuple(2*f for f in yz),
                       tuple(f + 2*g for f, g in zip(y2, z)))
        rhs = self.digit(self.identity(coefficients), 1)
        columns = [self.digit(self.multiply(derivatives[j], element), 0)
                   for (j, _, _), element in zip(INDICES, self.columns)]
        rows = [list(row) for row in zip(*columns)]
        return rows, rhs


def check_chart(slope, certificates, endpoint):
    marks = tuple((a, b-a) for a, b in zip((0, 1, 1), endpoint))
    chart = SlopeChart(slope, marks)
    residues = split_residues(slope.denominator)
    inputs = accepted = 0
    used = set()
    for a, q in residues:
        fixed = [((a, q)[m][j] >> i) & 1 for j, m, i in INDICES]
        # In a half-integral chart, odd indices vanish on the two split components.
        # Enumerate *all* their bits in the unramified normalized basis modulo 2.
        unknown = [k for k, (_, _, i) in enumerate(INDICES) if i % slope.denominator]
        for bits in product(range(2), repeat=len(unknown)):
            coefficients = fixed.copy()
            for k, bit in zip(unknown, bits):
                coefficients[k] = bit
            inputs += 1
            if any(chart.digit(chart.identity(coefficients), 0)):
                continue
            accepted += 1
            rows, rhs = chart.correction_matrix(coefficients)
            augmented = [row + [c] for row, c in zip(rows, rhs)]
            assert nmod_mat(rows, 2).rank() < nmod_mat(augmented, 2).rank()
            encoded = {sum(v << j for j, v in enumerate(row)) for row in augmented}
            matched = {k for k, patterns in enumerate(certificates) if patterns <= encoded}
            assert matched, "No Lean-checked contradiction occurs in this matrix"
            used.update(matched)
    expected = 22 if slope.denominator == 1 else 256
    assert accepted == expected
    print(f"endpoint={endpoint}, h={slope}: {len(residues)} split residues, {inputs} bit tuples, "
          f"{accepted} satisfy the identity modulo 2, 0 lift modulo 4.")
    return used


if __name__ == "__main__":
    counts = [len(split_residues(e)) for e in range(1, 7)]
    assert counts == [22, 1, 0, 0, 0, 0]
    print("Nonconstant split residues by reduced slope denominator 1..6:", counts)
    source = Path(__file__).with_name("TwoPointPrimaryTwo.lean").read_text()
    data = source.split("def contradictorySubsystems :", 1)[1].split(":= #[", 1)[1].split("\n]", 1)[0]
    certificates = [set(rows) for rows in literal_eval("[" + data + "]")]
    assert len(certificates) == 26
    used = set()
    endpoints = [(x, y, z) for x, y, z in product((1, 3), range(4), range(4))
                 if (x**3 + y*y*z + z*z - 2) % 4 == 0]
    assert endpoints == [(1, 0, 1), (1, 0, 3), (1, 2, 1), (1, 2, 3)]
    for endpoint in endpoints:
        for representative in (Fraction(1), Fraction(2), Fraction(3, 2), Fraction(5, 2)):
            used.update(check_chart(representative, certificates, endpoint))
    assert used == set(range(len(certificates)))
    print("All 2,224 matrices contain a Lean-certified contradictory subsystem.")
