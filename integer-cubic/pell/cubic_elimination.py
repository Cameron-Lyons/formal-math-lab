"""Eliminate the two shape parameters for the six cubic lifts through (0,1,1).

Run with: uv run --with python-flint==0.9.0 cubic_elimination.py
The derivation of the sextic and the required repeated-root condition is in
CubicElimination.md. All arithmetic here is over Z or a finite prime field.
"""

from pathlib import Path

from flint import fmpz_mpoly_ctx, fmpz_poly, nmod_poly


def sextic_discriminant_component():
    ctx = fmpz_mpoly_ctx.get(("S", "W", "B"), "lex")
    s, w, b = ctx.gens()

    def P(t):
        return t**3 - 6 * w * t - 2 * w - 4 * w**2

    def H(t):
        return t - t**2 + 4 * w

    A, G, C = P(b), H(b), w * (1 - 2 * w) ** 3
    Q, remainder = divmod(2 * C - H(s) ** 3, P(s))
    assert not remainder
    # The sextic is an S-independent nonzero multiple of (2−x³)/z−z.
    F = (
        A**3 * Q
        + 3 * A**2 * G * H(s) ** 2
        - 3 * A * G**2 * H(s) * P(s)
        + G**3 * P(s) ** 2
        - A * C * P(s)
    )
    assert F * P(s) == 2 * C * A**3 - (A * H(s) - G * P(s)) ** 3 - A * C * P(s) ** 2

    disc = F.discriminant("S")
    known = w**4 * H(b) ** 6 * P(b) ** 6 * (2 * w - 1) ** 8
    component, remainder = divmod(disc, known)
    assert not remainder and component.degrees() == (0, 28, 42)
    return component.primitive()[1]


def univariate_projection(component):
    projected = component.discriminant("B")
    assert projected.degrees() == (0, 1148, 0)
    coeffs = projected.to_dict()
    return fmpz_poly([coeffs.get((0, i, 0), 0) for i in range(1149)])


def factor_certificate(projection):
    factors = {}
    scalar, sqfree = projection.factor_squarefree()
    product = fmpz_poly([scalar])
    for f, m in sqfree:
        if f.degree() == 1:
            linear = {195: fmpz_poly([0, 1]), 660: fmpz_poly([-1, 2])}
            assert f == linear[int(m)]
        else:
            assert f.degree() not in factors
            factors[f.degree()] = f
            p = {37: 5, 62: 5, 44: 13}[f.degree()]
            reduced = nmod_poly([int(c) % p for c in f], p)
            assert reduced.degree() == f.degree() and all(
                reduced(a) != 0 for a in range(p)
            )
            print(
                f"degree {f.degree()}, multiplicity {m}: no projective root modulo {p}"
            )
        product *= f**m
    assert product == projection
    assert sorted((f.degree(), int(m)) for f, m in sqfree) == [
        (1, 195),
        (1, 660),
        (37, 1),
        (44, 3),
        (62, 2),
    ]
    return factors


def lean_data(factors):
    parts = [
        "module",
        "",
        "public section",
        "namespace SmallCubic.Eliminant",
        "",
        "/-! Integer coefficients of the three nonlinear factors, in ascending order.",
        "The elimination script checks this file against the exact discriminant. -/",
        "",
    ]
    for degree in sorted(factors):
        coeffs = list(factors[degree])
        parts.extend(
            [
                f"@[expose] def lead{degree} : Int := {coeffs[-1]}",
                f"@[expose] def low{degree} : List Int := [",
            ]
        )
        parts.extend(
            f"  {c}{',' if i < degree - 1 else ']'}" for i, c in enumerate(coeffs[:-1])
        )
        parts.append("")
    parts.append("end SmallCubic.Eliminant")
    return "\n".join(parts) + "\n"


if __name__ == "__main__":
    projection = univariate_projection(sextic_discriminant_component())
    factors = factor_certificate(projection)
    assert Path(__file__).with_name("CubicEliminantData.lean").read_text() == lean_data(
        factors
    )
    print("The only rational roots of the projected discriminant are 0 and 1/2.")
