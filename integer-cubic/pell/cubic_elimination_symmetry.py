"""Certify the reflection symmetry and the residue classes in the cubic Pell search.

Over F7, use s=(t+b*t²)/(1−3t²) and r=(1+2bt+3t²)/(1−3t²).
The identity r²=1+4bs+12s² makes x=C(s), z=Z(s), y=rE(s) a
nine-variable subsystem of the original eighteen-variable system.

Run with the python-flint dependency used by search_pell_mod.py.
"""

from itertools import product
from pathlib import Path

from flint import fmpz_mpoly_ctx, fmpz_poly, nmod_mat, nmod_poly

from search_pell_mod import cubic_candidates


def coordinates(poly, basis):
    """Solve for coefficients in the indicated independent polynomial basis."""
    p = int(poly.modulus())
    matrix = [[int(f[i]) for f in basis] for i in range(7)]
    rows = []
    for i in range(7):
        if nmod_mat([matrix[j] for j in rows + [i]], p).rank() > len(rows):
            rows.append(i)
    assert len(rows) == len(basis)
    coeffs = nmod_mat([matrix[i] for i in rows], p).solve(
        nmod_mat([[int(poly[i])] for i in rows], p)
    ).entries()
    values = [int(a) for a in coeffs]
    if sum(a * f for a, f in zip(values, basis)) == poly:
        return values
    return None


def symmetric_models(candidate):
    p = 7
    t = nmod_poly([0, 1], p)
    L = 1 - 3*t**2
    X, Y, Z = candidate
    for b in range(p):
        T = t + b*t**2
        R = 1 + 2*b*t + 3*t**2
        cubics = [T**j * L**(3-j) for j in range(4)]
        quadratics = [R * T**j * L**(2-j) for j in range(3)]
        c = coordinates(X, cubics)
        d = coordinates(Z, cubics)
        e = coordinates(Y, quadratics)
        if c is None or d is None or e is None:
            continue

        assert (c[0], d[0], e[0]) == (0, 1, 1)
        C, Z0, E = (nmod_poly(v, p) for v in (c, d, e))
        r2 = 1 + 4*b*t + 12*t**2
        assert C**3 + Z0**2 + r2 * E**2 * Z0 == 2
        # This makes gcd(X(t), Z(t)−L³) recover the factor t(1+bt).
        assert (C // t).gcd((Z0 - 1) // t) == 1
        columns = (
            [4*t*E**2*Z0]
            + [3*C**2*t**j for j in range(1, 4)]
            + [(r2*E**2+2*Z0)*t**j for j in range(1, 4)]
            + [2*r2*E*Z0*t**j for j in (1, 2)]
        )
        determinant = int(nmod_mat([
            [int(col[j]) for col in columns] for j in range(1, 10)
        ], p).det())
        assert determinant != 0
        yield b, C, Z0, E, determinant


def normalized_parameters(C, Z0):
    """Find the root θ of Z0 for which C(θ) is the chosen cube root of 2."""
    p = 7
    alpha = nmod_poly([0, 1], p)
    modulus = alpha**3 - 2
    assert all(modulus(j) != 0 for j in range(p))

    def evaluate(f, theta):
        return sum(int(c) * theta**j for j, c in enumerate(f)) % modulus

    roots = []
    for a, i, j in product(range(p), repeat=3):
        theta = a + i*alpha + j*alpha**2
        if evaluate(Z0, theta) == 0 and evaluate(C, theta) == alpha:
            roots.append((a, i, j))
    assert len(roots) == 1
    a, i, j = roots[0]
    assert i != 0
    inv = pow(i, -1, p)
    return j*inv % p, -a*inv % p


def first_lift_system(candidate, seed):
    """Construct the Jacobian and correction right-hand side modulo seven."""
    t = fmpz_poly([0, 1])
    L = 1 - 3*t**2
    X, Y, Z = (fmpz_poly(list(map(int, f))) for f in candidate)
    X[0], Y[0], Z[0] = seed
    residual = X**3 + Z*Y**2 + Z**2*L**3 - 2*L**9
    assert residual[0] == 0
    assert all(int(a) % 7 == 0 for a in residual)
    columns = [
        derivative*t**i
        for derivative in (3*X**2, 2*Z*Y, Y**2 + 2*Z*L**3)
        for i in range(1, 7)
    ]
    rows = [[int(f[i]) for f in columns] for i in range(1, 19)]
    rhs = [-int(residual[i]) // 7 for i in range(1, 19)]
    return nmod_mat(rows, 7), nmod_mat([[entry] for entry in rhs], 7)


def first_lift_ranks(candidate, seed):
    jacobian, rhs = first_lift_system(candidate, seed)
    augmented = [row + [rhs[i, 0]] for i, row in enumerate(jacobian.tolist())]
    return jacobian.rank(), nmod_mat(augmented, 7).rank()


def lean_witness_record(candidate, seed):
    """Reconstruct the exact input row of the Lean first-lift certificate."""
    jacobian, rhs = first_lift_system(candidate, seed)
    kernel, dimension = jacobian.transpose().nullspace()
    for j in range(dimension):
        left = nmod_mat([[kernel[i, j] for i in range(18)]], 7)
        if (left*rhs)[0, 0] != 0:
            assert not any((left*jacobian).entries())
            coeffs = [list(map(int, f)) for f in candidate]
            for f, c in zip(coeffs, seed):
                f[0] = c
            fields = [*coeffs, list(map(int, left.entries()))]
            return "  ⟨" + ", ".join(str(v) for v in fields) + "⟩"
    raise ValueError("the augmented system is consistent")



def exceptional_normalizations():
    """Check cubics with root ∛2 or ∛4 after an affine change of variable."""
    ring = fmpz_mpoly_ctx.get(("s", "a"), "lex")
    s, a = ring.gens()
    certificates = {
        1: {3: (6, 7), 24: (1, 5)},
        2: {3: (6, 7), 9: (1, 5), 33: (1, 5)},
    }
    for j in (1, 2):
        # P contains the normalized root and H/j evaluates there to ∛2.
        P = s**3 - 2**j
        A = a**3 - 2**j
        H, B = s**j, a**j
        Q, remainder = divmod(2*j**3 - H**3, P)
        assert not remainder
        F = (A**3*Q + 3*A**2*B*H**2 - 3*A*B**2*H*P
             + B**3*P**2 - j**3*A*P)
        assert F*P == 2*j**3*A**3 - (A*H - B*P)**3 - j**3*A*P**2
        disc = F.discriminant("s")
        assert disc.degrees()[0] == 0
        coeffs = disc.to_dict()
        U = fmpz_poly([coeffs.get((0, n), 0) for n in range(disc.degrees()[1]+1)])
        scalar, factors = U.factor()
        product_poly = fmpz_poly([scalar])
        found = {}
        for f, multiplicity in factors:
            product_poly *= f**multiplicity
            found[f.degree()] = multiplicity
            if f.degree() == 1:
                assert f == fmpz_poly([0, 1]) and multiplicity == 6*j
                continue
            expected, prime = certificates[j][f.degree()]
            assert multiplicity == expected
            reduced = nmod_poly([int(c) % prime for c in f], prime)
            assert reduced.degree() == f.degree()
            assert all(reduced(i) != 0 for i in range(prime))
        assert product_poly == U
        assert set(found) == {1, *certificates[j]}
        print(f"root (∛2)^{j}: the only rational discriminant root is a=0")


if __name__ == "__main__":
    count = 0
    for candidate in cubic_candidates(7, 3):
        (b, C, Z0, E, determinant), = symmetric_models(candidate)
        assert first_lift_ranks(candidate, (0, 1, 1)) == (18, 18)
        assert (C.degree(), Z0.degree(), E.degree()) == (3, 3, 2)
        assert (b*b - 3) % 7 != 0
        w, a = normalized_parameters(C, Z0)
        assert w**3 % 7 == 1 and a == 0
        print(f"X'(0)={candidate[0][1]}  b={b}  det={determinant}  (w,a)=({w},{a})")
        count += 1
    assert count == 6

    second_seed = (-2, 3, 1)
    records = []
    count = 0
    for candidate in cubic_candidates(7, 3, second_seed):
        ranks = first_lift_ranks(candidate, second_seed)
        assert ranks == (16, 17)
        records.append(lean_witness_record(candidate, second_seed))
        print(f"seed {second_seed}, X'(0)={candidate[0][1]}: "
              f"Jacobian and augmented ranks {ranks}")
        count += 1
    assert count == 6

    lean_file = Path(__file__).with_name("CubicLiftObstruction.lean")
    data_block = "private def data : Array Branch := #[\n" + ",\n".join(records) + "\n]"
    assert data_block in lean_file.read_text()

    exceptional_normalizations()
