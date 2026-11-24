"""Exact elimination for the cubic substitution through (1,0,1).

Run with: uv run --with python-flint==0.9.0 seed_one_elimination.py
The number-field normalization and the repeated factors are derived in SeedOne.md.
"""
from pathlib import Path

from flint import fmpq_poly, fmpz_mpoly_ctx, fmpz_poly, nmod_poly


def quintic(P, G, A, H, d, seed_factor):
    """Use J=P/A and C=(A*G-H*P)/(d*A). Divide the sextic by the seed root."""
    k = d**3
    Q, rem = divmod(2*k - G**3, P)
    assert not rem
    F = A**3*Q + 3*A**2*H*G**2 - 3*A*H**2*G*P + H**3*P**2 - A*k*P
    assert P*F == 2*k*A**3 - (A*G-H*P)**3 - A*k*P**2
    K, rem = divmod(F, seed_factor)
    assert not rem and K.degrees()[0] == 5
    return K


def as_univariate(f):
    coeffs = f.to_dict()
    degree, *others = f.degrees()
    assert all(n == 0 for n in others)
    return fmpz_poly([coeffs.get((i, *others), 0) for i in range(degree+1)])


def check_projective_obstruction(f, prime):
    reduced = nmod_poly([int(c) % prime for c in f], prime)
    assert reduced.degree() == f.degree()
    assert all(reduced(a) != 0 for a in range(prime))


def general_projection():
    ctx = fmpz_mpoly_ctx.get(("s", "w", "b"), "lex")
    s, w, b = ctx.gens()

    def P(t):
        return t**3-6*w**3*t-2*w**3-4*w**6

    def G(t):
        return t-t**2+4*w**3

    d = w*(1-2*w**3)
    A, H = P(b), G(b)-d
    K = quintic(P(s), G(s), A, H, d, s-b)
    known = w**8 * (2*w**3-1)**4 * A**4 * H**6
    component, rem = divmod(K.discriminant("s"), known)
    assert not rem and component.degrees() == (0, 68, 34)
    _, component = component.primitive()
    top = {k: v for k, v in component.to_dict().items() if k[-1] == 34}
    assert set(top) == {(0, 0, 34)} and abs(top[(0, 0, 34)]) == 4

    wb = fmpz_mpoly_ctx.get(("w", "b"), "lex")
    component = wb.from_dict({(i,j):c for (_,i,j),c in component.to_dict().items()})
    f = as_univariate(component.discriminant("b"))
    assert f.degree() == 2244
    scalar, factors = f.factor_squarefree()
    product = fmpz_poly([scalar])
    data = {}
    expected = {1: (330, None), 3: (442, 7), 90: (2, 11), 93: (1, 5), 105: (3, 7)}
    for factor, m in factors:
        degree = factor.degree()
        multiplicity, prime = expected[degree]
        assert m == multiplicity and degree not in data
        data[degree] = factor
        if degree == 1:
            assert factor == fmpz_poly([0, 1])
        else:
            check_projective_obstruction(factor, prime)
        if degree == 3:
            assert factor == fmpz_poly([-1, 0, 0, 2])
        product *= factor**m
    assert product == f and set(data) == set(expected)
    print("Degree-2244 projection: w=0 is the only rational root.")
    return {f"general{n}": data[n] for n in (90, 93, 105)}


def exceptional_projections():
    ctx = fmpz_mpoly_ctx.get(("s", "a"), "lex")
    s, a = ctx.gens()
    data = {}
    tables = {
        1: {1: (6, None), 3: (4, 7), 18: (1, 3)},
        2: {1: (1, None), 2: (6, 3), 3: (4, 7), 6: (1, 5), 27: (1, 3)},
    }
    for e, expected in tables.items():
        P, A, G, H = s**3-2**e, a**3-2**e, s**e, a**e-e
        K = quintic(P, G, A, H, e, s-a)
        disc = K.discriminant("s")
        coeffs = disc.to_dict()
        degree_s, degree_a = disc.degrees()
        assert degree_s == 0
        u = fmpz_poly([coeffs.get((0,i), 0) for i in range(degree_a+1)])
        scalar, factors = u.factor()
        product = fmpz_poly([scalar])
        assert sorted(f.degree() for f, _ in factors) == sorted(expected)
        for f, m in factors:
            multiplicity, prime = expected[f.degree()]
            assert m == multiplicity
            product *= f**m
            if prime is None:
                assert f == fmpz_poly([-e, 1])
            else:
                check_projective_obstruction(f, prime)
                data[f"special{e}d{f.degree()}"] = f
        assert product == u
    t = fmpq_poly([0,1])
    J = (t**3-4)/4
    C = (t**2-2*J)/2
    V, rem = divmod(2-C**3,J)
    assert not rem
    F = t**2*(t**3-4*t**2+4*t-12)
    assert 16*(V-J) == (t-2)*F and F.gcd(F.derivative()) == t
    print("Exceptional roots: a=1 forces degree drop; a=2 has gcd of degree one.")
    return data


def lean_data(factors):
    lines = ["module", "", "public section", "namespace SmallCubic.SeedOne", "",
             "/-! Primitive factors in ascending coefficient order.",
             "Recomputed and checked by seed_one_elimination.py. -/", ""]
    for key, f in sorted(factors.items()):
        lower = [str(c) for c in list(f)[:-1]]
        lines.append(f"@[expose] def {key}Lead : Int := {f.leading_coefficient()}")
        lines.append(f"@[expose] def {key}Low : List Int := [")
        lines.extend("  " + c + ("," if i+1 < len(lower) else "]") for i,c in enumerate(lower))
        lines.append("")
    return "\n".join([*lines, "end SmallCubic.SeedOne", ""])


if __name__ == "__main__":
    factors = general_projection() | exceptional_projections()
    assert Path(__file__).with_name("SeedOneData.lean").read_text() == lean_data(factors)
    print("All factor coefficients agree with the Lean certificate.")
