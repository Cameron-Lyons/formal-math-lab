"""Lift and certify the two-point residue class through (−2,3,1) through 7^500.

Run: uv run --with python-flint==0.9.0 python two_point_height.py
The input residue is independently enumerated by two_point_census.py --prime 7 --target 1.
"""

import argparse
from math import comb, isqrt
from pathlib import Path

from flint import fmpz_mat, fmpz_poly, nmod_mat

PRIME = 7
DENOM = fmpz_poly([1, 6, 6])
FIXED = 8 * DENOM**12
X_TOP = -2*6**4
Y_TOP = 3*6**3
W_TOP = 11*6**6
DEGREES = (1, 2, 4, 8, 16)
# Original numerators in the t coordinate. Z is recovered from X,Y.
RESIDUE = ([0, 3, 3, 4, 4, 1, 3, 4, 3], [1, 4, 0, 5, 6, 5, 3])


def change_chart(coefficients, degree, slope=3):
    # (1+slope*s)^degree f(s/(1+slope*s)).
    return [sum(c * comb(degree-j, k-j) * slope**(k-j)
                for j,c in enumerate(coefficients[:k+1])) for k in range(degree+1)]


def marked_coefficients(residue):
    x, y = (change_chart(f, d) for f,d in zip(residue,(8,6)))
    assert (x[0], y[0], x[-1] % PRIME, y[-1] % PRIME) == (0, 1, X_TOP % PRIME, Y_TOP % PRIME)
    return [c % PRIME for c in x[1:8] + y[1:6]]


def coefficients(variables, modulus):
    """Compute W and the twelve middle coefficients of W²−Y⁴+4X³−8D¹².

    The thirteen outer coefficients vanish by construction. All denominators
    are units modulo powers of seven.
    """
    x = fmpz_poly([0, *variables[:7], X_TOP])
    y = fmpz_poly([1, *variables[7:], Y_TOP])
    f = y**4 - 4*x**3 + FIXED

    def jet(rhs, root, length):
        coeffs = [root]
        reciprocal = pow(2*root,-1,modulus)
        for i in range(1,length):
            residual = rhs[i] - sum(coeffs[j]*coeffs[i-j] for j in range(1,i))
            coeffs.append(int(residual)*reciprocal % modulus)
        return coeffs

    low = jet([f[i] for i in range(7)], 3, 7)
    high = jet([f[24-i] for i in range(6)], W_TOP, 6)
    w = fmpz_poly(low + high[::-1])
    error = w**2 - f
    assert all(int(error[i]) % modulus == 0
               for i in (*range(7), *range(19,25)))
    middle = [error[i] for i in range(7,19)]
    return w, [int(c) % modulus for c in middle]


def lift(residue, precision):
    v = marked_coefficients(residue)
    p = PRIME
    f = coefficients(v,p*p)[1]
    assert all(c % p == 0 for c in f)
    columns = []
    for j in range(12):
        step = list(v)
        step[j] += p
        g = coefficients(step,p*p)[1]
        # Taylor's formula for the polynomial with coefficients in Z[1/66].
        columns.append([(a-b)//p % p for a,b in zip(g,f)])
    jacobian = nmod_mat(columns,p).transpose()
    det = int(jacobian.det())
    inverse = jacobian.inv()
    modulus = p
    for _ in range(1,precision):
        next_modulus = p*modulus
        f = coefficients(v,next_modulus)[1]
        assert all(c % modulus == 0 for c in f)
        digits = inverse * nmod_mat(12,1,[-c//modulus % p for c in f],p)
        v = [a + modulus*int(d) for a,d in zip(v,digits.entries())]
        modulus = next_modulus
    assert coefficients(v,modulus)[1] == [0]*12
    return v, modulus, det


def check_original(v, modulus):
    """Undo the chart change; independently verify all original coefficient and point equations."""
    y = fmpz_poly([1, *v[7:], Y_TOP])
    w, _ = coefficients(v, modulus)
    z = (w - y**2) * pow(2, -1, modulus)
    forms = ([0, *v[:7], X_TOP], list(y), list(z))
    x, y, z = [fmpz_poly([int(a) % modulus for a in change_chart(f, d, -3)])
               for f,d in zip(forms,(8,6,12))]
    ell = fmpz_poly([1, 0, -3])
    assert (x[0], y[0], z[0]) == (0, 1, 1)
    assert all(int(c) % modulus == 0 for c in x**3 + z*y**2 + z**2 - 2*ell**12)
    for f,d,value in zip((x,y,z),(4,3,6),(-2,3,1)):
        scaled = sum(f[j]*3**(2*d-j) for j in range(2*d+1))
        assert (scaled - value*6**d) % modulus == 0
    assert x[1] == v[0]
    if modulus == PRIME**500:
        lean = Path(__file__).with_name('TwoPointHeight.lean').read_text()
        assert f'def residue : ℤ := {v[0]}\n' in lean


def height_bound(value, modulus, degree):
    """Exclude every nonzero polynomial of degree ≤degree and height ≤bound.

    Every polynomial vanishing modulo modulus lies in the integer row lattice
    of basis below. If row i is the last nonzero row in a lattice combination,
    its squared norm is at least the squared length of the orthogonalized row i.
    The latter is the ratio of consecutive leading principal Gram determinants.
    """
    n = degree + 1
    powers = [pow(value,i,modulus) for i in range(1,n)]
    basis = fmpz_mat([[modulus] + [0]*degree] +
                     [[-w] + [int(i==j) for j in range(degree)] for i,w in enumerate(powers)])
    basis = basis.lll()
    # Membership and determinant directly verify that this really is the entire lattice.
    for row in basis.tolist():
        assert (row[0] + sum(c*w for c,w in zip(row[1:],powers))) % modulus == 0
    assert abs(basis.det()) == modulus
    gram = (basis * basis.transpose()).tolist()
    prev = 1
    min_sq = None
    for k in range(1,n+1):
        det = int(fmpz_mat([row[:k] for row in gram[:k]]).det())
        assert det > 0
        bound_squared = (det-1) // (n*prev)
        min_sq = bound_squared if min_sq is None else min(min_sq,bound_squared)
        prev = det
    return isqrt(min_sq)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--precision',type=int,default=500)
    args = parser.parse_args()
    assert args.precision >= 2
    v,modulus,det = lift(RESIDUE,args.precision)
    check_original(v,modulus)
    # As X(0)=0, the linear coefficient is unchanged by the chart change.
    print(f'x1 mod 7 = {v[0] % PRIME}, determinant mod 7 = {det}')
    for degree in DEGREES:
        bound = height_bound(v[0],modulus,degree)
        print(f'  degree ≤{degree}: height ≤10^{len(str(bound))-1} excluded')


if __name__ == '__main__':
    main()
