"""Certify the elliptic-logarithm inequalities used for the four affine cubics.

Requires python-flint 0.9.0. All integrals have Arb ball enclosures. The
lattice distance bound is exact regardless of the quality of LLL reduction.
"""

from fractions import Fraction
from math import lcm
from flint import acb, arb, ctx, fmpq_mat, fmpz_mat, fmpz_poly

from ellipticHeight import MODELS


def curve_roots(model):
    c2, c4, c6 = model
    roots = fmpz_poly([c6, c4, c2, 1]).complex_roots()
    real = [r for r, m in roots if r.imag.is_zero() and m == 1]
    pair = [r for r, m in roots if not r.imag.contains(0) and m == 1]
    assert len(real) == 1 and len(pair) == 2
    return real[0].real, pair[0], pair[1]


def unsigned_log(x, roots, at_root=False):
    # Integral from x to infinity of dX/sqrt(f(X)), by Carlson's definition
    # of RF. On this path the two nonreal square roots are conjugates.
    e, w, z = roots
    assert at_root or x > e
    d = 0 if at_root else x-e
    result = 2 * acb.elliptic_rf(d, x-w, x-z)
    assert result.imag.contains(0) and result.real > 0
    return result.real


def signed_log(point, roots, period):
    x, y = point
    value = unsigned_log(x, roots)
    assert value < period and (y > 0 or y < 0)
    return value if y > 0 else period - value


def round_certified(x):
    val = (x + arb(1)/2).floor().unique_fmpz()
    assert val is not None
    return int(val)


def certify_point_heights(model, basis, u, v, shift):
    k, l, m = model
    A = l - Fraction(k*k, 3)
    B = m - Fraction(k*l, 3) + Fraction(2*k**3, 27)
    j = 1728*4*A**3/(4*A**3+27*B**2)
    coords = [Fraction(1), -A/4, -B/16, j]
    den = lcm(*(z.denominator for z in coords))
    assert max(abs(z*den) for z in coords) < 2**100
    xs = [x+Fraction(k,3) for x,y in basis]
    assert all(max(abs(x.numerator), x.denominator) < 2**100 for x in xs)
    # X_inf = 4uv-shift+k/3 -2u*beta + 3*beta^2, beta^3=u*v^2.
    # The polynomial height bound h(X_inf) <= 2h(beta) + log(sum of
    # absolute cleared coefficients or denominator) is valid at all places.
    const = 4*u*v-shift+Fraction(k,3)
    assert (u*v*v)**2*(abs(const*3)+6*u+9+3)**3 < 2**300
    # Duplication on the short curve; clearing a common denominator bounds
    # the height at all nonarchimedean places by the projective-height rule.
    rows = [[1,0,-2*A,-8*B,A*A],[0,4,0,4*A,4*B]]
    d = lcm(*(Fraction(z).denominator for row in rows for z in row))
    assert max(sum(abs(z*d) for z in row) for row in rows) < 2**100
    # So h_X(2P) <= 4 h_X(P)+100, and the projective canonical height is
    # at most (5/2)(100+100/3) = 1000/3 (strict for these inputs).


def distance_check(logs, period, target, M, scale):
    a, b, c, w, t = [round_certified(scale*z) for z in [*logs, period, target]]
    basis = fmpz_mat([[1,0,0,a],[0,1,0,b],[0,0,1,c],[0,0,0,w]])
    reduced, transform = basis.lll(transform=True)
    assert transform*basis == reduced and abs(transform.det()) == 1
    inv = fmpq_mat(reduced.transpose()).inv()
    bounds = []
    for i in range(4):
        dual = [inv[i,j] for j in range(4)]
        coord = dual[-1]*t
        residue = coord.numerator % coord.denominator
        distance = Fraction(int(min(residue, coord.denominator - residue)), int(coord.denominator))
        norm = sum(z*z for z in dual)
        bounds.append(distance**2 * Fraction(int(norm.denominator), int(norm.numerator)))
    # A lattice point for a coefficient vector with |m_i| <= M has first
    # coordinates m_1,m_2,m_3. The last-coordinate rounding error is at
    # most (3M+|m_0|+1)/2 <= 3M+2, since |m_0| <= 3M+2.
    bound = max(bounds)
    assert bound > 3*M*M + (3*M+3)**2
    # Consequently |scale*L| > 1.
    return (bound.numerator // bound.denominator).bit_length()


def certify(u, v, shift, model, basis):
    k,l,m = model
    assert all(y*y == x**3+k*x*x+l*x+m for x,y in basis)
    assert (k, l, m) == (
        3*shift-8*u*v,
        3*shift**2-16*u*v*shift+5*u**2*v**2,
        shift**3-8*u*v*shift**2+5*u**2*v**2*shift+9*u**4*v**2+9*u**2*v**4+32*u**3*v**3,
    )
    certify_point_heights(model, basis, u, v, shift)
    roots = curve_roots(model)
    period = 2*unsigned_log(roots[0], roots, at_root=True)
    reflected = curve_roots((-k,l,-m))
    other_period = 2*unsigned_log(reflected[0], reflected, at_root=True)
    assert period > arb(1)/10 and period/other_period < 100
    alpha = (arb(u)/v).root(3)
    beta = v*alpha
    original_x = 4*u*v - 2*u*beta + 3*beta**2
    infinity_y = ((original_x**2-4*u*u*v*v)*alpha - 3*u*v*original_x - 6*u**3*v)/(2*u)
    x = original_x-shift
    assert (infinity_y**2-x**3-k*x*x-l*x-m).contains(0)
    target = signed_log((x,infinity_y), roots, period)
    logs = [signed_log(point, roots, period) for point in basis]
    stages = [(10**400, 10**1800), (250, 10**16)]
    bits = [distance_check(logs, period, target, M, scale) for M,scale in stages]
    print(f"r={u}/{v}, squared-distance lower bounds have bit lengths {bits}", flush=True)


if __name__ == "__main__":
    ctx.prec = 6800
    for case in MODELS:
        certify(*case)
