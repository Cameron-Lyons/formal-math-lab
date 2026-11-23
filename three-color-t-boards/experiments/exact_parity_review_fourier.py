#!/usr/bin/env python3
"""Independent read-only audit of the Fourier JSON exports; no counting run.

This does not import either Fourier generator or its polynomial/field helpers.
"""
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'experiments'


def mul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 7  # F2[X]/(X^2+X+1), computed without a lookup table.
    return result


def power(a, e):
    result = 1
    for _ in range(e):
        result = mul(result,a)
    return result


def windows():
    return [(row*row+j,(row+1)**2+j,(row+1)**2+j+1,(row+1)**2+j+2)
            for row in range(9) for j in range(2*row+1)]


def toggle(poly, term):
    if term in poly:
        poly.remove(term)
    else:
        poly.add(term)


def multiply(a, b):
    """Ordinary polynomial product modulo explicit free-variable z^3+1."""
    result = set()
    for left,right in itertools.product(a,b):
        exponents = dict(left)
        for variable,e in right:
            exponents[variable] = (exponents.get(variable,0)+e) % 3
        toggle(result,tuple(sorted((v,e) for v,e in exponents.items() if e)))
    return result


def evaluate(poly, values):
    result = 0
    powers = [(1,z,power(z,2)) for z in values]
    for monomial in poly:
        value = 1
        for variable,e in monomial:
            value = mul(value,powers[variable][e])
        result ^= value
    return result


def rank(rows):
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length()-1
            if pivot in basis:
                row ^= basis[pivot]
            else:
                basis[pivot] = row
                break
    return len(basis)


def main():
    paths = [OUT/f'exact_parity_math_fourier_{which}.json' for which in ('original','reduced')]
    data = [p.read_bytes() for p in paths]
    original,reduced = map(json.loads,data)
    assert original['variables']==100 and reduced['variables']==96
    assert {d['cell'] for d in original['domain_equations']} == set(range(100))
    assert len(original['domain_equations'])==100
    assert all(d['polynomial']=='z_cell^3+1' for d in original['domain_equations'])
    assert reduced['free_domain_equations']=='z_i^3+1 for all 96 free variables'
    free = reduced['free_original_cells']
    substitutions = {int(k):v for k,v in reduced['pivot_substitutions'].items()}
    assert len(free)==len(set(free))==96 and len(substitutions)==4
    assert set(free).isdisjoint(substitutions) and set(free)|set(substitutions)==set(range(100))
    assert all(len(s)==len(set(s)) and set(s)<=set(free) for s in substitutions.values())

    moments = {}
    for equation in original['moment_equations']:
        e = tuple(equation['role_exponents'])
        assert len(e)==4 and set(e)<=set(range(3)) and any(e)
        assert equation['rhs']==0 and e not in moments
        terms = [tuple(tuple(pair) for pair in term) for term in equation['terms']]
        assert len(terms)==len(set(terms))
        expected = set()
        for window in windows():
            toggle(expected,tuple(sorted((cell,x) for cell,x in zip(window,e) if x)))
        assert set(terms)==expected
        moments[e] = expected
    conjugates = {tuple(2*x%3 for x in e) for e in moments}
    assert len(moments)==40 and not (set(moments)&conjugates)
    assert set(moments)|conjugates == set(itertools.product(range(3),repeat=4))-{(0,0,0,0)}
    linear = [poly for e,poly in moments.items() if sum(e)==1]
    assert len(linear)==4 and rank([sum(1 << term[0][0] for term in p) for p in linear])==4

    exported = {}
    for equation in reduced['remaining_equations']:
        poly = set()
        for text in equation['terms']:
            number = int(text,16)
            assert number >= 0 and number >> 192 == 0
            term = []
            for i in range(96):
                exponent = number >> (2*i) & 3
                assert exponent != 3
                if exponent:
                    term.append((i,exponent))
            assert tuple(term) not in poly
            poly.add(tuple(term))
        assert equation['label'] not in exported
        exported[equation['label']] = poly
    assert len(exported)==40

    index = {cell:i for i,cell in enumerate(free)}
    expressions = {cell:{((i,1),)} for cell,i in index.items()}
    expressions.update({cell:{((index[source],1),) for source in sources}
                        for cell,sources in substitutions.items()})
    squares = {cell:multiply(poly,poly) for cell,poly in expressions.items()}
    expected_labels = set()
    for e,poly in moments.items():
        result = set()
        for term in poly:
            part = {()}
            for cell,exponent in term:
                part = multiply(part,expressions[cell] if exponent==1 else squares[cell])
            result.symmetric_difference_update(part)
        if sum(e)==1:
            assert not result
        else:
            label = 'moment:'+','.join(map(str,e))
            expected_labels.add(label)
            assert result==exported[label],label
    for cell in substitutions:
        result = multiply(expressions[cell],squares[cell])
        toggle(result,())
        label = f'pivot_domain:{cell}'
        expected_labels.add(label)
        assert result==exported[label],label
    assert expected_labels==set(exported)

    def audit_board(rows):
        values = [int(c)+1 for row in rows for c in row]
        patterns = Counter(tuple(values[cell] for cell in window) for window in windows())
        valid = len(patterns)==81
        ordinary_failures = sum(evaluate(poly,values)!=0 for poly in moments.values())
        partial = [values[cell] for cell in free]
        reduced_failures = sum(evaluate(poly,partial)!=0 for poly in exported.values())
        recovered = all(values[cell]==__import__('functools').reduce(int.__xor__,
                        (values[source] for source in sources),0)
                        for cell,sources in substitutions.items())
        assert all(power(value,3)==1 for value in values)
        assert (ordinary_failures==0)==valid
        if valid:
            assert recovered and reduced_failures==0
        return dict(valid=valid,distinct_patterns=len(patterns),
                    original_failed_moments=ordinary_failures,
                    reduced_failed_equations=reduced_failures,pivots_recovered=recovered)

    seeds = json.loads((ROOT/'sources/anc/certificates.json').read_text())['ternary_seeds']
    checked = 0
    for rows,permutation,reflection in itertools.product(seeds,itertools.permutations('012'),(False,True)):
        image = [''.join(permutation[int(c)] for c in (row[::-1] if reflection else row)) for row in rows]
        assert audit_board(image)['valid']
        checked += 1
    counterexample = audit_board(json.loads((OUT/'exact_structure_counterexample.json').read_text())['rows'])
    assert not counterexample['valid'] and counterexample['pivots_recovered']
    assert counterexample['reduced_failed_equations'] > 0
    report = dict(status='PASS',source_hashes={str(p.relative_to(ROOT)):hashlib.sha256(b).hexdigest()
                  for p,b in zip(paths,data)},original_moments_regenerated=40,
                  frobenius_pairs_verified=40,linear_rank=4,
                  reduced_equations_symbolically_verified=40,valid_board_images_checked=checked,
                  counterexample=counterexample,no_counting_trial_performed=True)
    (OUT/'exact_parity_review_fourier_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
