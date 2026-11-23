#!/usr/bin/env python3
"""Measure exact F2 substitution inputs; never invokes a polynomial solver."""
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path

from exact_parity_math_fourier import original_equations, eliminate, unpack, packed_term
from exact_parity_math import windows

ROOT = Path(__file__).resolve().parent


def main():
    source = ROOT / 'exact_parity_math_fourier_reduced.json'
    document = json.loads(source.read_text())
    free, substitutions, reduced = eliminate(original_equations())
    assert free == document['free_original_cells']
    assert {str(k): v for k, v in substitutions.items()} == document['pivot_substitutions']
    assert [(e['label'], {int(t, 16) for t in e['terms']})
            for e in document['remaining_equations']] == reduced
    all_moments = []
    for label, poly in reduced:
        if label.startswith('moment:'):
            exponents = tuple(map(int, label.split(':')[1].split(',')))
            all_moments.append((label, poly))
            squared = {packed_term((i, 2*e) for i, e in unpack(t)) for t in poly}
            all_moments.append(('moment:' + ','.join(str(2*e % 3) for e in exponents), squared))
    assert len(all_moments) == 72
    all80 = all_moments + [(label, p) for label, p in reduced if label.startswith('pivot_domain:')]

    # Independently substitute all geometric moments, including the eight
    # equations that become zero, rather than trusting Frobenius pairing.
    index = {cell: i for i, cell in enumerate(free)}
    lookup = dict(all_moments)
    zero_equations = 0
    for exponents in product(range(3), repeat=4):
        if not any(exponents):
            continue
        result = set()
        for window in windows(10):
            fixed = [(index[cell], e) for cell, e in zip(window, exponents)
                     if e and cell not in substitutions]
            pivots = [(cell, e) for cell, e in zip(window, exponents)
                      if e and cell in substitutions]
            assert len(pivots) <= 1
            terms = [fixed] if not pivots else [fixed + [(index[v], pivots[0][1])]
                                               for v in substitutions[pivots[0][0]]]
            for pairs in terms:
                term = packed_term(pairs)
                if term in result:
                    result.remove(term)
                else:
                    result.add(term)
        if not result:
            zero_equations += 1
        else:
            assert result == lookup['moment:' + ','.join(map(str, exponents))]
    assert zero_equations == 8

    def monomial(term):
        return '*'.join(f'x{i+1}' + (f'^{e}' if e != 1 else '')
                        for i, e in unpack(term)) or '1'

    def describe(polys):
        monomials = set().union(*(p for _, p in polys))
        equations = [f'x{i+1}^3-1' for i in range(96)]
        equations += ['+'.join(monomial(t) for t in sorted(p)) for _, p in polys]
        text = ','.join(f'x{i+1}' for i in range(96)) + '\n2\n' + ',\n'.join(equations) + '\n'
        degree = lambda t: sum(e for _, e in unpack(t))
        return dict(variables=96, free_cubic_domains=96, remaining_equations=len(polys),
                    generators=len(equations), non_domain_terms=sum(len(p) for _, p in polys),
                    moment_terms=sum(len(p) for label, p in polys if label.startswith('moment:')),
                    pivot_domain_terms={label: len(p) for label, p in polys if label.startswith('pivot_domain:')},
                    all_polynomial_terms=192 + sum(len(p) for _, p in polys),
                    distinct_nondomain_monomials=len(monomials),
                    largest_equation_terms=max(len(p) for _, p in polys),
                    maximum_term_total_degree=max(map(degree, monomials)),
                    non_domain_degree_histogram=dict(sorted(Counter(degree(t) for _, p in polys for t in p).items())),
                    input_utf8_bytes=len(text.encode()), input_sha256=hashlib.sha256(text.encode()).hexdigest(),
                    maximum_line_bytes=max(map(len, text.splitlines())))

    report = dict(status='ANALYSIS_ONLY_NO_SOLVER',
                  source_reduced_json_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  export_matches_fresh_reconstruction=True,
                  all80_independently_substituted_from_geometry=True,
                  vanishing_unary_and_squared_unary_equations=zero_equations,
                  pivot_substitution_lengths={k: len(v) for k, v in substitutions.items()},
                  selected40=describe(reduced), all80=describe(all80),
                  memory=dict(exponent_bytes_per_hash_slot_100_variables=202,
                              exponent_bytes_per_hash_slot_96_variables=194,
                              bytes_saved_per_hash_at_2_pow_22=8*2**22,
                              MiB_saved_per_hash_at_2_pow_22=32,
                              MiB_saved_two_hashes_at_2_pow_22=64))
    (ROOT / 'exact_msolve_elimination_analysis.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
