#!/usr/bin/env python3
"""Independent audit of the four disjoint linear sign branches; no solver."""
import hashlib
from itertools import product
import json
from pathlib import Path

from exact_msolve_review import parse_polynomial

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mono(*indices):
    return tuple(indices.count(i) for i in range(97))


def decode(record):
    result = {}
    for coefficient, encoded in record['terms']:
        word = int(encoded, 16)
        assert 0 <= word < (1 << (4*97)) and coefficient in (1, 2)
        term = tuple((word >> (4*i)) & 15 for i in range(97))
        assert term not in result
        result[term] = coefficient
    return result


def rank(rows):
    pivots = {}
    for source in rows:
        row = dict(source)
        while row:
            pivot = min(row)
            if pivot not in pivots:
                pivots[pivot] = {i: c*row[pivot] % 3 for i, c in row.items()}
                break
            scale = row[pivot]
            for i, c in pivots[pivot].items():
                value = (row.get(i, 0)-scale*c) % 3
                if value:
                    row[i] = value
                else:
                    row.pop(i, None)
    return len(pivots)


def main():
    manifest_path = HERE/'exact_f3_sign_branches_manifest.json'
    assert digest(manifest_path) == '9ecb49f828699a3966c0349bddb4bc4f57cc163b65ba1855770357bf2e39d2c7'
    manifest = json.loads(manifest_path.read_text())
    translation = json.loads((HERE/'exact_f3_translation_model.json').read_text())
    order = json.loads((HERE/'exact_f3_order_selected.json').read_text())
    forms = {int(c): {int(v): a for v, a in f.items()}
             for c, f in translation['normalized_color_linear_forms'].items()}
    windows = [( (r-1)**2+j, r*r+j, r*r+j+1, r*r+j+2)
               for r in range(1, 10) for j in range(2*r-1)]
    assert windows[0] == (0, 1, 2, 3) and windows[3] == (3, 6, 7, 8)
    differences = []
    for a, b in zip(windows[0], windows[3]):
        variables = set(forms[a]) | set(forms[b])
        differences.append({v: (forms[a].get(v, 0)-forms[b].get(v, 0)) % 3
                            for v in variables if (forms[a].get(v, 0)-forms[b].get(v, 0)) % 3})
    assert [rank(differences[:k+1]) for k in range(4)] == [1, 2, 3, 4]
    partition = [0]*4
    canonical = set()
    for delta in product(range(3), repeat=4):
        if not any(delta):
            continue
        branch = next(i for i, value in enumerate(delta) if value)
        sign = delta[branch]
        normalized = tuple(sign*x % 3 for x in delta)
        assert normalized[branch] == 1 and not any(normalized[:branch])
        assert tuple(sign*x % 3 for x in normalized) == delta
        canonical.add((branch, sign, normalized))
        partition[branch] += 1
    assert partition == [54, 18, 6, 2] and len(canonical) == 80
    inputs = []
    for entry in manifest['branches']:
        k = entry['branch_id']
        for label, base_name, permutation in [
                ('natural', 'exact_f3_translation_e3.ms', list(range(97))),
                ('minfill', 'exact_f3_order_selected.ms', order['old_index_to_new_index']+[96])]:
            path = HERE/entry[label+'_input']
            assert digest(path) == entry[label+'_sha256']
            model_path = path.with_suffix('.json')
            model = json.loads(model_path.read_text())
            assert model['branch_id'] == k and model['variables'] == 97
            assert model['generators'] == 179+k and model['count_divisor'] == model['count_multiplier'] == 1
            assert not model['prefix'] and not model['fixed_original_cells'] and not model['quintic_selector_included']
            assert model['individual_field_domain_count'] == 97
            header, prime, body = path.read_text().split('\n', 2)
            assert header == ','.join(f'x{i+1}' for i in range(97)) and prime == '3'
            source_body = (HERE/base_name).read_text().split('\n', 2)[2].rstrip('\n')
            assert body.startswith(source_body+',\n')
            extra_text = body[len(source_body)+2:].strip().split(',\n')
            expected = [{mono(96): 2, mono(96,96,96): 1}, {mono(): 2, mono(96,96): 1}]
            for i in range(k+1):
                p = {mono(permutation[v]): c for v, c in differences[i].items()}
                if i == k:
                    p[mono()] = 2
                expected.append(p)
            assert len(extra_text) == k+3
            assert [parse_polynomial(text, 97, 3) for text in extra_text] == expected
            assert [decode(record) for record in model['additional_equations']] == expected
            for cell in range(100):
                expected_color = {mono(95): 1}
                expected_color.update({mono(permutation[v], 96): c for v, c in forms[cell].items()})
                assert decode(model['original_color_bilinear_polynomials'][str(cell)]) == expected_color
            inputs.append(dict(branch_id=k, order=label, input_sha256=digest(path),
                               metadata_sha256=digest(model_path), generators=179+k))
    report = dict(status='PASS', inputs=inputs, independent_constraint_ranks=[1,2,3,4],
                  difference_space_partition=partition, finite_sign_bijections_checked=80,
                  original_color_polynomials_checked=800, source_polynomial_bodies_preserved=8,
                  unrestricted_count=None, note='Difference-space sizes are not board-count ratios.')
    (HERE/'exact_f3_sign_branches_review_results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'inputs'}, indent=2))


if __name__ == '__main__':
    main()
