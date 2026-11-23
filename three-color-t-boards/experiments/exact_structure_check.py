#!/usr/bin/env python3
"""Independent finite checks for the exact-structure research note."""
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def geometric_patterns(rows):
    cells = {(j-r, -r): int(c) for r, row in enumerate(rows) for j, c in enumerate(row)}
    result = []
    for x, y in cells:
        points = [(x, y+1), (x-1, y), (x, y), (x+1, y)]
        if all(p in cells for p in points):
            result.append(tuple(cells[p] for p in points))
    return result


def valid(rows, n):
    patterns = geometric_patterns(rows)
    assert len(patterns) == n**4
    assert set(patterns) == set(product(range(n), repeat=4))


def encode_rotors(rows, n):
    values = [tuple(map(int, row)) for row in rows]
    boundary = (values[0][0],) + tuple(c for row in values[1:] for c in row[:2])
    output = defaultdict(list)
    for r in range(1, len(rows)):
        for j in range(2*r-1):
            p = (values[r-1][j],) + values[r][j:j+3]
            output[p[:3]].append(p[3])
    assert set(output) == set(product(range(n), repeat=3))
    assert all(sorted(p) == list(range(n)) for p in output.values())
    return boundary, {k: tuple(v) for k,v in output.items()}


def decode_rotors(n, boundary, output):
    rows = [[boundary[0]]]
    used = Counter()
    for r in range(1, n*n+1):
        row = list(boundary[2*r-1:2*r+1])
        for j in range(2*r-1):
            state = (rows[-1][j], row[j], row[j+1])
            if used[state] == n:
                return None, (r, j+2, state)
            row.append(output[state][used[state]])
            used[state] += 1
        rows.append(row)
    return [''.join(map(str,row)) for row in rows], None


def check_marginal_counterexample():
    data = json.loads((ROOT/'experiments/exact_structure_counterexample.json').read_text())
    rows = data['rows']
    assert [len(r) for r in rows] == list(range(1,20,2))
    patterns = geometric_patterns(rows)
    assert len(patterns) == 81
    counts = Counter(patterns)
    for p in product(range(3), repeat=4):
        expected = 1 if 0 in p else (2 if p.count(2)%2 == 0 else 0)
        assert counts[p] == expected
    for omit in range(4):
        marginal = Counter(p[:omit]+p[omit+1:] for p in patterns)
        assert len(marginal) == 27 and set(marginal.values()) == {3}
    assert len(counts) == 73
    print('ternary counterexample: four uniform 3-marginals; 65 singleton, 8 doubled, 8 absent quadruples PASS')


def check_best_obstructions():
    a = ['0','000','00111','1101011','111001000']
    b = ['0','000','01001','1101111','001011000']
    valid(a,2); valid(b,2)
    def local(rows):
        return rows[2][0]+rows[3][:3], rows[2][1]+rows[3][1:3]
    assert local(a) == ('0110','010') and local(b) == ('0110','110')
    print('same local quadruple at same position has different next state PASS')

    sources = json.loads((ROOT/'sources/anc/certificates.json').read_text())['ternary_seeds']
    def local_ternary(rows):
        return rows[6][3]+rows[7][3:6], rows[6][4]+rows[7][4:6]
    valid(sources[2],3); valid(sources[3],3)
    assert local_ternary(sources[2]) == ('1110','210')
    assert local_ternary(sources[3]) == ('1110','110')
    print('ternary same-position quadruple also has different next state PASS')
    source = sources[0]
    valid(source,3)
    boundary, original = encode_rotors(source,3)
    changed = dict(original)
    assert changed[0,0,0] == (0,1,2)
    changed[0,0,0] = (1,0,2)
    assert all(original[k][-1] == changed[k][-1] for k in original)
    assert decode_rotors(3,boundary,original)[0] == source
    assert decode_rotors(3,boundary,changed) == (None,(3,2,(0,0,0)))
    print('same boundary and all last outputs; original succeeds, non-last swap fails PASS')

    common = ['222012012','00021112200','0010010022200',
              '110202021201011','02121111210221022','2221101121221000202']
    a = ['2','122','11011','1200012'] + common
    b = ['2','122','11012','1200011'] + common
    valid(a,3); valid(b,3)
    ba, ra = encode_rotors(a,3); bb, rb = encode_rotors(b,3)
    assert ba == bb and a[-1] == b[-1]
    assert [k for k in ra if ra[k] != rb[k]] == [(2,0,1)]
    assert ra[2,0,1] == (1,2,0) and rb[2,0,1] == (2,1,0)
    print('same boundary and bottom; two valid boards have opposite rotor-permutation signs PASS')


def check_binary_implication():
    for parity in (0,1):
        histogram = Counter()
        for bottom in product(range(2),repeat=9):
            rows = [bottom]
            for _ in range(4):
                low = rows[-1]
                rows.append(tuple(parity ^ low[j] ^ low[j+1] ^ low[j+2]
                                  for j in range(len(low)-2)))
            words = [''.join(map(str,row)) for row in rows[::-1]]
            counts = Counter(geometric_patterns(words))
            histogram[max(counts.values())] += 1
        assert sum(histogram.values()) == 512 and min(histogram) >= 3
        print(f'binary parity={parity}: all 512 bottoms rejected; maximum-multiplicity histogram {dict(sorted(histogram.items()))} PASS')


def check_quasigroups():
    perms = list(permutations(range(3)))
    latin = [tuple(c for row in rows for c in row) for rows in product(perms, repeat=3)
             if all(len({rows[x][y] for x in range(3)}) == 3 for y in range(3))]
    affine2 = {tuple((a*x+b*y+d)%3 for x in range(3) for y in range(3))
               for a,b in product((1,2),repeat=2) for d in range(3)}
    assert len(latin) == 12 and set(latin) == affine2
    # x,y index each 2D slice; z chooses the slice.
    cubes = {tuple(slices[z][3*x+y] for x in range(3) for y in range(3) for z in range(3))
             for slices in product(latin,repeat=3)
             if all(len({slices[z][3*x+y] for z in range(3)}) == 3
                    for x in range(3) for y in range(3))}
    affine3 = {tuple((a*x+b*y+c*z+d)%3 for x in range(3) for y in range(3) for z in range(3))
               for a,b,c in product((1,2),repeat=3) for d in range(3)}
    assert len(cubes) == 24 and cubes == affine3
    print('all 12 Latin squares and all 24 ternary quasigroups of order 3 are affine PASS')
    log = (ROOT/'experiments/exact_structure_ca_all.log').read_text().splitlines()
    summaries = [line for line in log if line.startswith('colors=')]
    assert len(summaries) == 24
    expected = {f'{a},{b},{c},{d}' for a,b,c in product((1,2),repeat=3) for d in range(3)}
    found = set()
    for line in summaries:
        values = dict(term.split('=',1) for term in line.split())
        assert values['colors'] == '3' and values['status'] == 'COMPLETE' and values['solutions'] == '0'
        found.add(values['rule'])
    assert found == expected
    print('CA log covers every one of the 24 affine rules with COMPLETE zero results PASS')


def check_boundary_rank():
    points = [(0,1),(-1,0),(0,0),(1,0)]
    classes = defaultdict(list)
    for indices in product(range(3),repeat=4):
        support = [(x,y,k) for (x,y),k in zip(points,indices) if k]
        if support:
            minx = min(x for x,y,k in support); miny = min(y for x,y,k in support)
            key = tuple(sorted((x-minx,y-miny,k) for x,y,k in support))
        else:
            key = ()
        classes[key].append(indices)
    assert len(classes) == 71
    assert sum(len(v)-1 for v in classes.values()) == 10
    assert Counter(len(v) for v in classes.values()) == {1:65, 2:4, 4:2}
    print('universal local boundary divergences: dimension 10, bulk rank 71 PASS')


if __name__ == '__main__':
    check_marginal_counterexample()
    check_best_obstructions()
    check_binary_implication()
    check_quasigroups()
    check_boundary_rank()
