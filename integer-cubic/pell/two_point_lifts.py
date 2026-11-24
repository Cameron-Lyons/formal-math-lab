"""Check marked lifting equations and intersections with all 27 lines."""

import argparse
import json
from pathlib import Path

from flint import fmpz_poly, nmod_mat, nmod_poly

from quartic_first_lifts import DEGREES, T, residual, poly_triple, translate
from quartic_local_geometry import intersections


def line_tests(p):
    t = nmod_poly([0, 1], p)
    tests = [(f.degree(), intersections(f, False, p)) for f, _ in (t**3-2).factor()[1]]
    if p == 13:
        # Slopes coincide in pairs in this characteristic. The two values of
        # r distinguish the lines with the same slope.
        roots = [r for r in range(p) if (3*r*r+6*r+2) % p == 0]
        tests.extend((f.degree(), intersections(f, True, p, r))
                     for f, _ in (t**12-3).factor()[1] for r in roots)
    else:
        tests.extend((f.degree(), intersections(f, True, p))
                     for f, _ in (t**24+540*t**12-108).factor()[1])
    assert sum(size for size, _ in tests) == 27
    return tests


def errors(triple, mark):
    body = residual(triple)
    assert body[0] == 0 and body.degree() <= 24
    endpoint = [sum(int(f[j])*3**(d-j) for j in range(d+1))-value*6**(d//2)
                for f, d, value in zip(triple, DEGREES, mark)]
    return [int(body[j]) for j in range(1, 25)] + endpoint


def lift(hit, p, mark, precision):
    triple = tuple(fmpz_poly(hit[k]) for k in 'xyz')
    x, y, z = triple
    derivs = (3*x*x, 2*y*z, y*y+2*z)
    columns = [f*T**j for f, d in zip(derivs, DEGREES) for j in range(1, d+1)]
    rows = [[int(c[i]) for c in columns] for i in range(1, 25)]
    rows.extend([int(i == k)*3**(d-j) for i, d in enumerate(DEGREES) for j in range(1, d+1)]
                for k in range(3))
    jac = nmod_mat(rows, p)
    rank = jac.rank()
    err = errors(triple, mark)
    assert all(e % p == 0 for e in err)
    aug = nmod_mat([r + [-e//p] for r, e in zip(rows, err)], p).rank()
    if rank != aug or rank < 26:
        return dict(rank=rank, augmented=aug)
    pivot_rows = next([i for i in range(27) if i != omit] for omit in range(27)
                      if nmod_mat([r for i, r in enumerate(rows) if i != omit], p).rank() == rank)
    inv = nmod_mat([rows[i] for i in pivot_rows], p).inv()
    modulus = p
    for k in range(1, precision):
        digits = [-e//modulus % p for e in err]
        vec = inv * nmod_mat([[digits[i]] for i in pivot_rows], p)
        if jac * vec != nmod_mat([[n] for n in digits], p):
            return dict(rank=rank, augmented=aug, obstruction_exponent=k+1)
        triple = translate(triple, modulus, poly_triple([int(n) for n in vec.entries()]))
        modulus *= p
        err = errors(triple, mark)
        assert all(e % modulus == 0 for e in err)
    return dict(rank=rank, augmented=aug, verified_exponent=precision)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('census', type=Path)
    parser.add_argument('--precision', type=int, default=8)
    args = parser.parse_args()
    for line in args.census.read_text().splitlines():
        record = json.loads(line)
        p, mark = record['prime'], record['endpoint']
        tests = line_tests(p)
        print(f"p={p}, second endpoint={mark}, residues={len(record['hits'])}")
        for hit in record['hits']:
            degrees = [test([hit[k] for k in 'xyz']) for _, test in tests]
            print('  X coefficients', hit['x'], 'line degrees', degrees,
                  'lift', lift(hit, p, mark, args.precision))


if __name__ == '__main__':
    main()
