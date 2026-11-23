#!/usr/bin/env python3
"""Audit a full p29 Singular input against geometry without running Singular."""
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def main():
    path = ROOT/'experiments/exact_algebra_backend_full_prime29_all.sing'
    raw = path.read_bytes()
    script = raw.decode()
    header = script.split('ideal I=\n',1)[0]
    assert header=='ring R=29,('+','.join(f'x{i+1}' for i in range(100))+'),dp;\n'
    assert 'qring' not in script and 'minpoly' not in script
    polynomials = script.split('ideal I=\n',1)[1].split(';',1)[0].split(',\n')
    assert len(polynomials)==180
    assert polynomials[:100]==[f'x{i+1}^3-1' for i in range(100)]
    exponents = [e for e in itertools.product(range(3),repeat=4) if any(e)]
    windows = [(r*r+j,(r+1)**2+j,(r+1)**2+j+1,(r+1)**2+j+2)
               for r in range(9) for j in range(2*r+1)]
    for e,polynomial in zip(exponents,polynomials[100:]):
        expected = Counter(tuple(sorted((cell,k) for cell,k in zip(w,e) if k)) for w in windows)
        actual = Counter()
        for term in polynomial.split('+'):
            coefficient = 1
            monomial = []
            for factor in term.split('*'):
                if factor.isdigit():
                    coefficient *= int(factor)
                else:
                    match = re.fullmatch(r'x(\d+)(?:\^(\d+))?',factor)
                    assert match,factor
                    cell,exponent = int(match[1])-1,int(match[2] or 1)
                    assert 0<=cell<100 and exponent in (1,2)
                    monomial.append((cell,exponent))
            actual[tuple(sorted(monomial))] += coefficient
        assert {k:v%29 for k,v in actual.items() if v%29} == \
               {k:v%29 for k,v in expected.items() if v%29},e
    assert 'ideal G=std(I);' in script or 'ideal G=slimgb(I);' in script
    result = dict(status='PASS',script=str(path.relative_to(ROOT)),
                  script_sha256=hashlib.sha256(raw).hexdigest(),
                  coefficient_field='ordinary F29',variables=100,fixed_prefix_rows=0,
                  domain_equations=100,nonconstant_moment_equations=80,
                  geometric_placements=81,all_input_polynomials_independently_regenerated=True,
                  boolean_reduction=False,symmetry_normalization=False,count_multiplier=1,
                  count_status='NO_COUNT_COMPUTED_BY_AUDIT')
    (ROOT/'experiments/exact_prime_fourier_full_import_review.json').write_text(
        json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
