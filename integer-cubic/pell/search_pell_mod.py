"""Search Pell conics through (x,y,z)=(0,1,1) over F_7 and lift cubic candidates.

Run with: uv run --with python-flint==0.9.0 search_pell_mod.py

Use u=U/L, v=V/L with L=1−Dt², U=1+Dt², V=2t on u²−Dv²=1.
The seed corresponds to t=0. The cubic search requires full pole order for x.
"""
from itertools import product

from math import gcd

from flint import fmpz_poly, nmod_mat, nmod_poly
from flint.utils.flint_exceptions import DomainError


def test_affine_y():
    p = 7
    residues = range(p)
    square_residues = {k*k % p for k in residues}
    t = nmod_poly([0, 1], p)
    L, U, V = 1 - 2*t**2, 1 + 2*t**2, 2*t
    # v²=(u²−1)/2, so the four displayed terms span quadratics
    # vanishing at (1,0), after multiplying by L².
    basis = [U**2-L**2, U*V, (U-L)*L, V*L]
    four_x_cubes = [
        4 * sum(k*f for k, f in zip(coeffs, basis))**3
        for coeffs in product(residues, repeat=4)
    ]
    tested = hits = 0
    for a, b in product(residues, repeat=2):
        if a == 0 and b == 0:
            continue
        Y = L + a*(U-L) + b*V
        base = L**2 * Y**4 + 8 * L**6
        for cube in four_x_cubes:
            # L^6 (y^4 + 8 − 4x^3) must be a square in F_7[t].
            # Its value at t=0 is 9 mod 7, so it is nonzero.
            scalar, factors = (base-cube).factor_squarefree()
            tested += 1
            if int(scalar) in square_residues and all(e % 2 == 0 for _, e in factors):
                hits += 1
    print(f"{tested} candidates, {hits} polynomial squares")


def possible_z(factors, p, z0=1):
    """All polynomial divisors of degree at most six with specified nonzero Z(0)."""
    divisors = [nmod_poly([1], p)]
    for factor, multiplicity in factors:
        powers = [factor**j for j in range(min(multiplicity, 6//factor.degree())+1)]
        divisors = [d*q for d in divisors for q in powers if q[0] and d.degree()+q.degree() <= 6]
    for divisor in divisors:
        yield divisor * (z0*pow(int(divisor[0]), -1, p) % p)


def cubic_candidates(p, D, seed=(0, 1, 1)):
    """Use x=X/L³, y=Y/L³, z=Z/L³ with numerators of degree at most six."""
    t = nmod_poly([0, 1], p)
    x0, y0, z0 = seed
    if z0*z0 + y0*y0*z0 + x0**3 != 2 or z0 % p == 0:
        raise ValueError("the seed must solve the cubic and have nonzero z modulo p")
    L = 1-D*t**2
    L3, const = L**3, 2*L**9
    for coeffs in product(range(p), repeat=6):
        X = nmod_poly([x0, *coeffs], p)
        if X.gcd(L).degree() > 0:
            continue
        F = const-X**3
        _, factors = F.factor()
        # Z divides F and Y² = F/Z − Z L³ by the original cubic.
        for Z in possible_z(factors, p, z0):
            Y2 = F//Z - Z*L3
            if Y2 and (Y2.degree() > 12 or Y2.degree() % 2):
                continue
            try:
                Y = Y2.sqrt()
            except DomainError:
                continue
            if int(Y[0]) != y0 % p:
                Y = -Y
            assert int(Y[0]) == y0 % p and Z*(Y**2+Z*L3) == F
            yield X, Y, Z
            if y0 % p == 0 and Y and p != 2:
                yield X, -Y, Z


def lift(candidate, p, D, exponent):
    """Correct the 18 nonconstant coefficients, keeping the seed fixed."""
    t = fmpz_poly([0, 1])
    L = 1-D*t**2
    X, Y, Z = (fmpz_poly(list(map(int, f.coeffs()))) for f in candidate)
    columns = [s*t**i for s in (3*X**2, 2*Y*Z, Y**2+2*Z*L**3) for i in range(1, 7)]
    jacobian = nmod_mat([[int(s[i]) % p for s in columns] for i in range(1, 19)], p)
    # All six candidates reported for D=3 have an invertible Jacobian.
    inverse = jacobian.inv()
    modulus = p
    for _ in range(1, exponent):
        error = X**3 + Z*Y**2 + Z**2*L**3 - 2*L**9
        assert all(int(c) % modulus == 0 for c in error)
        rhs = nmod_mat([[-(int(error[i])//modulus) % p] for i in range(1, 19)], p)
        digits = [int(c) for c in (inverse*rhs).entries()]
        X, Y, Z = [f+modulus*fmpz_poly([0, *digits[start:start+6]])
                   for f, start in ((X, 0), (Y, 6), (Z, 12))]
        modulus *= p
    residual = X**3 + Z*Y**2 + Z**2*L**3 - 2*L**9
    assert all(int(c) % modulus == 0 for c in residual)
    return X, Y, Z


def small_fraction(value, modulus, bound):
    """Find a numerator and denominator of size ≤ bound, or return None."""
    assert 2*bound**2 < modulus
    r, s = modulus, int(value) % modulus
    j, k = 0, 1
    while s > bound:
        q = r//s
        r, s, j, k = s, r-q*s, k, j-q*k
    if 0 < abs(k) <= bound and gcd(k, modulus) == 1 and gcd(s, k) == 1:
        return s, k
    return None


if __name__ == "__main__":
    test_affine_y()
    p, exponent, bound = 7, 71, 10**10
    for D in (2, 3):
        candidates = list(cubic_candidates(p, D))
        print(f"D={D}: {len(candidates)} full-pole cubic candidates modulo {p}")
        for X, Y, Z in candidates:
            lifted = lift((X, Y, Z), p, D, exponent)
            small = sum(small_fraction(f[i], p**exponent, bound) is not None
                        for f in lifted for i in range(1, 7))
            print(f"  X={X}: lifted modulo {p}^{exponent}, "
                  f"{small}/18 coefficients of rational height ≤ {bound}")
