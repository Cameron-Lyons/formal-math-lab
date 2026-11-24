"""Check the bad-reduction charts at 7 for both marked quartic Pell problems.

Run with uv run --with python-flint==0.9.0 python two_point_alternate.py.
All coordinates are in ascending coefficient order.
"""

from itertools import product

from flint import fmpz_poly, nmod_mat, nmod_poly
from flint.utils.flint_exceptions import DomainError

P = 7
DEGREES = (4, 3, 6)
SEED = (0, 1, 1)
TARGETS = ((1, 0, -1), (-2, 3, 1))
T = fmpz_poly([0, 1])


def ordinary(point):
    """All ordinary triples of the bounded degrees at the specified point."""
    x0, y0, z0 = point
    rows = []
    # For constant x the marked, nonzero product z(z+y²) is constant.
    assert (2-x0**3) % P
    for coefficients in product(range(P), repeat=4):
        x = nmod_poly([x0, *coefficients], P)
        if x.degree() <= 0:
            continue
        f = 2-x**3
        divisors = [x**0]
        for g, e in f.factor()[1]:
            divisors = [h*g**i for h in divisors for i in range(e+1)
                        if h.degree()+i*g.degree() <= 6]
        for h in divisors:
            if f.degree()-h.degree() > 6:
                continue
            z = h*(z0*pow(int(h[0]), -1, P) % P)
            try:
                y = (f//z-z).sqrt()
            except DomainError:
                continue
            if y.degree() > 3:
                continue
            for root in (y, -y) if y else (y,):
                if int(root[0]) == y0 % P:
                    assert z**2+z*root**2+x**3 == 2
                    rows.append((x, root, z))
    const = tuple(nmod_poly([c], P) for c in point)
    return [const, *rows]


def leading(triple):
    return tuple(int(f[d]) for f, d in zip(triple, DEGREES))


def scale(triple, a):
    return tuple(f(nmod_poly([0, a], P)) for f in triple)


def denominator_branch(left, right, point):
    """Represent the split branches as P and P+Q, with the marked constants."""
    result = [(fmpz_poly(list(map(int, f))), fmpz_poly(list(map(int, g-f))))
              for f, g in zip(left, right)]
    for (f, g), a, b in zip(result, SEED, point):
        f[0], g[0] = a, b-a
    return result


def add(left, right):
    return tuple(a+b for a, b in zip(left, right))


def multiply(left, right, h):
    # With w=u-1-v=2hs, v²=(1+2hs)v+2hs+2h²s².
    f, q = left
    g, r = right
    return f*g+(2*h*T+2*h*h*T*T)*q*r, f*r+q*g+(1+2*h*T)*q*r


def residual(branch, h):
    x, y, z = branch
    a, b = add(multiply(x, multiply(x, x, h), h),
               multiply(z, add(z, multiply(y, y, h)), h))
    assert a[0] == 2 and b[0] == 0 and a.degree() <= 12 and b.degree() <= 11
    return [int(a[i]) for i in range(1, 13)]+[int(b[i]) for i in range(1, 12)]


def first_correction(branch):
    base = residual(branch, 0)
    assert all(v % P == 0 for v in base)
    cols = []
    for component in (0, 1):
        for i, degree in enumerate(DEGREES):
            for power in range(1, degree-component+1):
                dest = [[fmpz_poly(f), fmpz_poly(q)] for f, q in branch]
                dest[i][component][power] += P
                cols.append(residual(dest, 0))
    cols.append(residual(branch, P))
    matrix = nmod_mat([[int((c[i]-b)//P) for c in cols] for i, b in enumerate(base)], P)
    rhs = nmod_mat([[-v//P] for v in base], P)
    augmented = nmod_mat([r+[rhs[i, 0]] for i, r in enumerate(matrix.tolist())], P)
    return matrix, rhs, augmented.rank()


WITNESSES = (
    (0, 6, 2, 0, 3, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 0, 0, 3, 0, 1, 0, 0, 0),
    (0, 0, 0, 5, 4, 5, 0, 0, 0, 0, 1, 2, 0, 0, 0, 2, 4, 5, 1, 0, 0, 0, 1),
)


def main():
    left = ordinary(SEED)
    assert len(left) == 7
    for k, point in enumerate(TARGETS):
        right = ordinary(point)
        assert len(right) == (19, 43)[k]
        pairs = [(i, j) for i, a in enumerate(left) for j, b in enumerate(right)
                 if (i or j) and leading(a) == leading(b)]
        assert len(pairs) == 6
        i, j = min(pairs, key=lambda ij: leading(left[ij[0]]))
        a, b = left[i], right[j]
        assert leading(a) == (3, 3, 2)
        assert all((scale(a, s), scale(b, s)) in [(left[m], right[n]) for m, n in pairs]
                   for s in range(1, P))
        assert len({leading(scale(a, s)) for s in range(1, P)}) == 6
        branch = denominator_branch(a, b, point)
        matrix, rhs, augmented = first_correction(branch)
        witness = nmod_mat([list(WITNESSES[k])], P)
        assert (matrix.rank(), augmented) == ((19, 20), (18, 19))[k]
        assert not any((witness*matrix).entries()) and (witness*rhs)[0, 0]
        print(f"{point}: {len(right)-1} nonconstant triples; six compatible pairs, "
              f"one orbit; first-correction ranks {matrix.rank()} and {augmented}.")


if __name__ == "__main__":
    main()
