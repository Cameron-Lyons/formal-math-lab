#!/usr/bin/env python3
"""Check the reduced Boolean export against original moments and valid boards."""
from pathlib import Path
import json
import random

from exact_parity_math import moments, windows

HERE = Path(__file__).resolve().parent


def value(poly, assignment):
    return sum((assignment & term) == term for term in poly) % 2


def main():
    exported = json.loads((HERE/'exact_parity_math_reduced_3.json').read_text())
    equations = {entry['label']:{int(t,16) for t in entry['terms']}
                 for entry in exported['equations']}
    substitutions = {int(v):{int(t,16) for t in terms}
                     for v,terms in exported['pivot_substitutions'].items()}
    free = exported['original_free_variables']
    original = moments(10,3)
    def compress(full):
        return sum(((full >> v) & 1) << i for i,v in enumerate(free))
    def decode(partial):
        full = sum(((partial >> i) & 1) << v for i,v in enumerate(free))
        for v,p in substitutions.items():
            full |= value(p,partial) << v
        return full
    def from_colors(flat):
        return sum(1 << (2*i+int(c)) for i,c in enumerate(flat) if c != '2')
    certificate = json.loads((HERE/'exact_structure_gauge_certificate.json').read_text())
    boards = set()
    for entry in certificate['boards']:
        flat = entry['flat']; boards.add(flat)
        boards.add(''.join(flat[r*r:(r+1)*(r+1)][::-1] for r in range(10)))
    for flat in boards:
        assert len({tuple(flat[c] for c in w) for w in windows(10)}) == 81
        full = from_colors(flat); partial = compress(full)
        assert decode(partial) == full
        assert all(value(p,partial) == 0 for p in equations.values())
    rng = random.Random(0xA1F)
    for _ in range(100):
        # Assign the96 free cells valid ternary colors; decoded pivot cells
        # may violate their palettes, which the exported equations detect.
        partial = 0
        for cell in range(96):
            color = rng.randrange(3)
            if color < 2:
                partial |= 1 << (2*cell+color)
        full = decode(partial)
        for labels,p in original:
            direct = value(p,full)
            if sum(label >= 0 for label in labels) == 1:
                assert direct == 0
            else:
                assert direct == value(equations['moment:'+','.join(map(str,labels))],partial)
        for cell in range(100):
            direct = ((full >> (2*cell)) & 3) == 3
            assert direct == value(equations[f'cell:{cell}'],partial)
    witness = json.loads((HERE/'exact_structure_counterexample.json').read_text())
    full = from_colors(''.join(witness['rows']))
    failed = [labels for labels,p in original if value(p,full)]
    assert failed == [(1,1,1,1)]
    binary = json.loads((HERE/'exact_parity_math_binary_result.json').read_text())
    assert binary['assignments_checked'] == 2**21 and binary['solutions'] == 168
    assert binary['geometric_anf_mismatches'] == 0
    report = {'status':'PASS','valid_ternary_boards_checked':len(boards),
              'random_substitution_checks':100,
              'triple_marginal_counterexample_failed_moments':failed,
              'binary_exhaustive_audit':binary}
    (HERE/'exact_parity_math_check_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
