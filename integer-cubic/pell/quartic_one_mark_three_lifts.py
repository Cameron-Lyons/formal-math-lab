"""One marked point at 3, in the numerator and integral Pell-coordinate charts.

Run: uv run --with python-flint==0.9.0 python quartic_one_mark_three_lifts.py
"""

from collections import Counter, defaultdict
from itertools import combinations, product

from flint import fmpz_poly, nmod_mat, nmod_poly
from quartic_local_geometry import T, candidates


class LinearSystem:
    """Solve the same matrix over F_3 for many correction right-hand sides."""

    def __init__(self, columns):
        matrix = nmod_mat(list(map(list, zip(*columns, strict=False))), 3)
        n = matrix.ncols()
        rank = matrix.rank()
        augmented = [
            r + [int(i == j) for j in range(24)] for i, r in enumerate(matrix.tolist())
        ]
        rows = nmod_mat(augmented, 3).rref()[0].tolist()
        self.operations = [
            [(j, int(x)) for j, x in enumerate(r[n:]) if x] for r in rows
        ]
        self.pivots = [next(i for i, x in enumerate(r[:n]) if x) for r in rows[:rank]]
        basis, dimension = matrix.nullspace()
        self.kernel = [[int(basis[i, j]) for i in range(n)] for j in range(dimension)]
        self.n = n

    def solve(self, rhs):
        values = [sum(rhs[j] * c for j, c in row) % 3 for row in self.operations]
        if any(values[len(self.pivots) :]):
            return None
        result = [0] * self.n
        for pivot, value in zip(self.pivots, values, strict=False):
            result[pivot] = value
        return result

    def solutions(self, center, sparse=False):
        if sparse:
            # Used only to produce witnesses. An unsuccessful sparse search
            # is never accepted as evidence that a lift is impossible.
            supports = (
                indices
                for k in range(4)
                for indices in combinations(range(len(self.kernel)), k)
            )
            digits = (
                (indices, u)
                for indices in supports
                for u in product((1, 2), repeat=len(indices))
            )
        else:
            indices = range(len(self.kernel))
            digits = ((indices, u) for u in product(range(3), repeat=len(indices)))
        for indices, u in digits:
            yield [
                (
                    x
                    + sum(
                        a * self.kernel[j][i] for j, a in zip(indices, u, strict=False)
                    )
                )
                % 3
                for i, x in enumerate(center)
            ]


def integer_poly(f):
    return fmpz_poly(list(map(int, f)))


def numerator_bases():
    target = nmod_poly([2], 3)
    for row in product(range(3), repeat=8):
        x = nmod_poly([0, *row], 3)
        for y, z in candidates(x, target, 3):
            yield tuple(integer_poly(f) for f in (x, y, z))


def component_triples(marked):
    """Ordinary reductions on u=1 or u=-1, indexed by the three top coefficients."""
    result = defaultdict(list)
    for ys in product(range(3), repeat=3 if marked else 4):
        y = nmod_poly(([1] if marked else []) + list(ys), 3)
        for zs in product(range(3), repeat=6 if marked else 7):
            z = nmod_poly(([1] if marked else []) + list(zs), 3)
            cube = 2 - z * (z + y * y)
            if cube.derivative():
                continue
            x = nmod_poly([cube[3 * i] for i in range(5)], 3)
            assert x**3 == cube
            top = tuple(int(f[d]) for f, d in zip((x, y, z), (4, 3, 6), strict=False))
            result[top].append(tuple(integer_poly(f) for f in (x, y, z)))
    return result


def pell_bases():
    plus, minus = component_triples(True), component_triples(False)
    assert (sum(map(len, plus.values())), sum(map(len, minus.values()))) == (27, 387)
    for k, triples in plus.items():
        for a, b in product(triples, minus[k]):
            yield tuple(zip(a, b, strict=False))


class Numerator:
    degrees = (8, 6, 12)
    target = 2 * (1 - 3 * T * T) ** 12

    @staticmethod
    def residual(base):
        x, y, z = base
        f = x**3 + z * (z + y * y) - Numerator.target
        assert f[0] == 0 and f.degree() <= 24
        return [int(f[i]) for i in range(1, 25)]

    @staticmethod
    def increment(base, digits, scales):
        return tuple(
            f + m * fmpz_poly([0, *digits[l:r]])
            for f, m, (l, r) in zip(
                base, scales, ((0, 8), (8, 14), (14, 26)), strict=False
            )
        )


class Pell:
    degrees = (4, 3, 6)

    @staticmethod
    def multiply(a, b):
        # Representatives store the values at the formal symbols u=+1 and -1.
        # Multiplication in the conic algebra contributes the same correction
        # to both components. 4^(-1) is needed only to precision 81.
        c = 3 * pow(4, -1, 81) * T * T * (a[0] - a[1]) * (b[0] - b[1])
        return (a[0] * b[0] + c, a[1] * b[1] + c)

    @classmethod
    def residual(cls, base):
        x, y, z = base
        a = cls.multiply(x, cls.multiply(x, x))
        b = cls.multiply(
            z, tuple(k + l for k, l in zip(z, cls.multiply(y, y), strict=False))
        )
        f, g = (k + l - 2 for k, l in zip(a, b, strict=False))
        assert not f[0] and f[12] == g[12] and max(f.degree(), g.degree()) <= 12
        return [int(f[i]) for i in range(1, 13)] + [int(g[i]) for i in range(12)]

    @classmethod
    def increment(cls, base, digits, scales):
        v = iter(digits)
        result = []
        for (p, q), d, m in zip(base, cls.degrees, scales, strict=False):
            left = [0] + [next(v) for _ in range(d)]
            right = [next(v) for _ in range(d)] + left[-1:]
            result.append((p + m * fmpz_poly(left), q + m * fmpz_poly(right)))
        assert next(v, None) is None
        return result


def rhs(chart, w, modulus):
    residual = chart.residual(w)
    assert all(x % modulus == 0 for x in residual)
    return [-x // modulus % 3 for x in residual]


def matrix(chart, w, first):
    # The x digits lag the y,z digits by one power of 3. Finite differences
    # give the Jacobian columns since all nonlinear terms vanish one level up.
    scales = (0, 3, 3) if first else (3, 9, 9)
    modulus = 3 if first else 9
    base = chart.residual(w)
    columns = []
    for j in range(8 if first else 0, 26):
        direction = [int(i == j) for i in range(26)]
        shifted = chart.increment(w, direction, scales)
        diff = [b - a for a, b in zip(base, chart.residual(shifted), strict=False)]
        assert all(x % modulus == 0 for x in diff)
        columns.append([x // modulus % 3 for x in diff])
    return LinearSystem(columns)


def level_81(chart, at9, system, center):
    # The top-degree equation modulo 81 forces both X_8 and Z_12
    # to vanish modulo 9. See OneMarkLocalThree.lean.
    if chart is Numerator and (
        at9[2][12] % 9 or (center[7] % 3 and all(v[7] == 0 for v in system.kernel))
    ):
        return False
    for v in system.solutions(center, sparse=True):
        at27 = chart.increment(at9, v, (3, 9, 9))
        q = system.solve(rhs(chart, at27, 27))
        if q is not None:
            witness = chart.increment(at27, q, (9, 27, 27))
            rhs(chart, witness, 81)
            return True
    raise AssertionError("No explicit lift or obstruction for this residue")


def check(chart, bases):
    counts = Counter()
    primary = Counter()
    for w in bases:
        counts[3] += 1
        first = matrix(chart, w, True)
        v = first.solve(rhs(chart, w, 3))
        if v is None:
            continue
        counts[9] += 1
        x, y, z = w if chart is Numerator else tuple(c[0] for c in w)
        if chart is Pell:
            primary[tuple(map(str, (x, y, z)))] += 1
        if not x:
            # In the Pell lattice this census stops at 9 on the constant
            # primary component. The numerator chart has an exact constant map.
            continue
        counts["nonconstant"] += 1
        system = matrix(chart, w, False)
        has27 = False
        for u in first.solutions(v):
            at9 = chart.increment(w, [0] * 8 + u, (0, 3, 3))
            q = system.solve(rhs(chart, at9, 9))
            if q is not None:
                has27 = True
                if level_81(chart, at9, system, q):
                    counts[81] += 1
                    break
        counts[27] += has27
    return counts, primary


if __name__ == "__main__":
    rational, _ = check(Numerator, numerator_bases())
    pell, components = check(Pell, pell_bases())
    assert rational == {3: 759, 9: 21, "nonconstant": 20, 27: 18, 81: 16}
    assert pell == {3: 1161, 9: 56, "nonconstant": 36, 27: 28, 81: 28}
    assert components == {
        ("0", "1", "1"): 20,
        ("2*x^2", "1", "x^3 + 1"): 18,
        ("2*x^2", "1", "2*x^3 + 1"): 18,
    }
    print("Numerator residues above nonconstant X through moduli 9,27,81: 20,18,16.")
    print(
        "Pell pairs through modulus 9: 56/1161; primary components:", dict(components)
    )
    print("Pell pairs above nonconstant primary X through moduli 9,27,81: 36,28,28.")
