"""Local tests of the normalized quartic Pell identity at 2, 3, and 5.

Run with: uv run --with python-flint==0.9.0 quartic_local_geometry.py
The optional --all-lines verifies the sloped line intersection profiles as well.
See QuarticGeometry.md for the exact hypotheses of each test.
"""

import argparse
import ast
import json
from collections import Counter
from itertools import product
from pathlib import Path

from flint import fmpz_poly, fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx, nmod_mat, nmod_poly

from quartic_rational_search import admissible_pairs, full_mod_five

T = fmpz_poly([0, 1])
L = 1-3*T*T


def candidates(x, target, p):
    f = target-x**3
    assert f != 0
    if p != 2:
        yield from admissible_pairs(f)
        return
    # Z(0)=1 excludes every factor vanishing at zero. W(0) can vanish at 2.
    factors = [(g, m) for g, m in f.factor()[1] if int(g[0])]
    for powers in product(*(range(m+1) for _, m in factors)):
        z = nmod_poly([1], p)
        for (g, _), e in zip(factors, powers):
            z *= g**e
        w = f//z
        if max(z.degree(), w.degree()) > 12:
            continue
        square = w-z
        if square.derivative() != 0:
            continue
        y = nmod_poly([square[2*i] for i in range(7)], p)
        assert y[0] == 1 and z*(z+y*y) == f
        yield y, z


def ranks(polys, p):
    x, y, z = (fmpz_poly(list(map(int, f))) for f in polys)
    error = x**3 + z*y**2 + z**2 - 2*L**12
    assert error[0] == 0 and all(c % p == 0 for c in error)
    columns = [f*T**i for f, n in ((3*x*x, 8), (2*y*z, 6), (y*y+2*z, 12))
               for i in range(1, n+1)]
    rows = [[int(c[i]) for c in columns] for i in range(1, 25)]
    rhs = [-int(error[i])//p for i in range(1, 25)]
    return nmod_mat(rows, p).rank(), nmod_mat([r+[b] for r,b in zip(rows,rhs)], p).rank()


def check_small_prime(p):
    t = nmod_poly([0, 1], p)
    target = 2*(1-3*t*t)**12
    count = Counter()
    survivors = []
    binary_models = set()
    for row in product(range(p), repeat=8):
        x = nmod_poly([0, *row], p)
        if p == 2 and not x(1):
            continue
        for y, z in candidates(x, target, p):
            a, b = ranks((x,y,z), p)
            count[a,b] += 1
            if p == 2:
                binary_models.add(tuple(tuple(map(int, f)) for f in (x,y,z)))
            if a == b:
                survivors.append((x,y,z))
    if p == 2:
        assert count == {(18,19): 4, (20,21): 3}
        lean = Path(__file__).with_name("QuarticBadTwo.lean").read_text()
        section = lean.split("private def branches : Array Branch := #[", 1)[1].split("\n]", 1)[0]
        certified = []
        for line in section.splitlines():
            if "⟨" in line:
                record = ast.literal_eval("[" + line.split("⟨")[1].split("⟩")[0] + "]")
                certified.append(tuple(tuple(row) for row in record[:3]))
        assert len(certified) == 7 and binary_models == set(certified)
    if p == 3:
        assert sum(count.values()) == 759 and len(survivors) == 21
        assert all(x.degree() <= 4 and y.degree() <= 3 and z.degree() <= 6 for x,y,z in survivors)
    print(f"p={p}: {sum(count.values())} residues; {len(survivors)} extend modulo {p*p}.")


def intersections(modulus, sloped, p, slope_parameter=None):
    if modulus.degree() == 1:
        K = fq_default_ctx(p)
        alpha = K(-int(modulus[0]))
    else:
        K = fq_default_ctx(modulus=fmpz_mod_poly_ctx(p)(list(map(int, modulus))), var='a')
        alpha = K.gen()
    R = fq_default_poly_ctx(K)
    t = R.gen()
    ell = 1-3*t*t
    if sloped:
        a = alpha
        v = (-(K(6)/a**12 + K(11))/K(26) if slope_parameter is None
             else K(slope_parameter))
        b, c, d = a**4*v, -a**3, -a**6*(3*v+1)
    else:
        a, b, c, d = K(0), alpha, K(0), K(0)
    assert a**3+c == 0 and 3*a*a*b+c*c+d == 0
    assert 3*a*b*b+2*c*d == 0 and b**3+d*d == 2

    def degree(polys):
        x, y, z = (R(list(map(int, f))) for f in polys)
        f = x-R(a)*y*ell-R(b)*ell**4
        g = z-R(c)*y*ell**3-R(d)*ell**6
        return f.gcd(g).degree() + min(8-f.degree(), 12-g.degree())

    return degree


def check_five(all_lines):
    p = 5
    t = nmod_poly([0,1], p)
    ell = 1-3*t*t
    target = 2*ell**12
    line_orbits = [(f, False) for f, _ in (t**3-2).factor()[1]]
    if all_lines:
        line_slope_poly = T**24+540*T**12-108
        assert line_slope_poly.factor()[1] == [(line_slope_poly, 1)]
        line_orbits += [(f, True) for f, _ in (t**24+540*t**12-108).factor()[1]]
    tests = [intersections(f, slope, p) for f, slope in line_orbits]
    profiles = Counter()
    after_lift = Counter()
    for row in full_mod_five():
        x = nmod_poly([0,*row], p)
        order = 4-x.gcd(ell**4).degree()//2
        for y, z in candidates(x, target, p):
            vals = tuple(g((x,y,z)) for g in tests)
            profiles[order, vals] += 1
            if min(vals) >= 4:
                a, b = ranks((x,y,z), p)
                after_lift[order,a,b] += 1
    assert sum(profiles.values()) == 157
    assert after_lift == {(4,24,24):80, (4,22,23):24, (2,20,20):2, (1,16,16):2, (0,12,12):1}
    print("p=5: 157 residues; 109 pass line degrees; 85 also pass the lift modulo 25.")
    print("order of x, line-intersection profile, number of triples:")
    for (order, profile), count in sorted(profiles.items()):
        print(order, profile, count)


def check_seven_lines():
    p = 7
    t = nmod_poly([0,1], p)
    orbits = [(f, False) for f,_ in (t**3-2).factor()[1]]
    orbits += [(f, True) for f,_ in (t**24+540*t**12-108).factor()[1]]
    tests = [intersections(f, slope, p) for f, slope in orbits]
    records = Path(__file__).with_name("quartic_orbits_mod7.jsonl").read_text().splitlines()
    assert len(records) == 12
    for row in map(json.loads, records):
        assert all(test([row[k] for k in "xyz"]) == 4 for test in tests)
    print("p=7: every line has intersection degree 4 in all 12 quartic orbits.")


def check_integral_pell_basis():
    """Use the integral Pell ring itself, retaining the nilpotent in characteristic 2."""
    def mul(g, h):
        a, b = g
        c, d = h
        return (a*c + 2*(T*T-T)*b*d, a*d+b*c-2*(1+T)*b*d)
    def add(g, h):
        return (g[0]+h[0], g[1]+h[1])
    def scale(g, n):
        return (g[0]*n, g[1]*n)
    def coeffs(g):
        return [int(g[0][i]) for i in range(1,13)]+[int(g[1][i]) for i in range(12)]
    def classes(n):
        return [nmod_poly(list(c), 2) for c in product(range(2), repeat=n)]
    def lift(f):
        return fmpz_poly(list(map(int, f)))

    t = nmod_poly([0,1], 2)
    count = Counter()
    survivors = []
    for x, y, z in product(classes(4), classes(3), classes(6)):
        x, y, z = t*x, 1+t*y, 1+t*z
        if x**3+y*y*z+z*z != 0:
            continue
        for qx in classes(4):
            qz, rem = divmod(x*x*qx,y*y)
            if rem or qz.degree() >= 6:
                continue
            for qy in classes(3):
                X, Y, Z = ((lift(f), lift(g)) for f,g in ((x,qx),(y,qy),(z,qz)))
                error = add(add(mul(X,mul(X,X)), mul(Z,add(mul(Y,Y),Z))),(-2,0))
                rhs = coeffs(error)
                assert all(v % 2 == 0 for v in rhs)
                derivatives = (scale(mul(X,X),3), scale(mul(Y,Z),2), add(mul(Y,Y),scale(Z,2)))
                columns = [coeffs(mul(g,b)) for g,n in zip(derivatives,(4,3,6))
                           for b in ([(T**i,0) for i in range(1,n+1)]+[(0,T**i) for i in range(n)])]
                rows = list(zip(*columns))
                a = nmod_mat(rows,2).rank()
                b = nmod_mat([list(row)+[-v//2] for row,v in zip(rows,rhs)],2).rank()
                count[a,b] += 1
                if a == b:
                    survivors.append((x,y,z,qx,qy,qz))
    assert count == {(12,13):992, (12,12):32, (20,21):16}
    assert all(x == 0 and y == 1 and z == 1 and qz == 0 for x,y,z,qx,qy,qz in survivors)
    print("Integral (u,v) model at 2: 1040 residues; 32 lift modulo 4, all constant on w=0.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all-lines", action="store_true")
    args = parser.parse_args()
    check_small_prime(2)
    check_small_prime(3)
    check_integral_pell_basis()
    check_five(args.all_lines)
    if args.all_lines:
        check_seven_lines()
