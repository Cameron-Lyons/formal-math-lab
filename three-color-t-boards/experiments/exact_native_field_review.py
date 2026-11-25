#!/usr/bin/env python3
"""Independent centered-geometry audit of the natural-F3 exported model."""
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def add(a, b, scale=1):
    out = dict(a)
    for word, coefficient in b.items():
        value = (out.get(word, 0)+scale*coefficient) % 3
        if value:
            out[word] = value
        else:
            out.pop(word, None)
    return out


@lru_cache(maxsize=None)
def normalize(word):
    out, shift = 0, 0
    while word:
        exponent = word & 15
        if exponent:
            out |= (1+(exponent-1) % 2) << shift
        shift += 4
        word >>= 4
    return out


def multiply(a, b):
    out = {}
    for u, c in a.items():
        for v, d in b.items():
            word = normalize(u+v)
            value = (out.get(word, 0)+c*d) % 3
            if value:
                out[word] = value
            else:
                out.pop(word, None)
    return out


def decode(equation):
    out = {}
    for coefficient, encoded in equation['terms']:
        word = int(encoded, 16)
        assert coefficient in (1, 2) and 0 <= word < 1 << (4*96) and word not in out
        out[word] = coefficient
    return out


def main():
    path = HERE/'exact_f3_math_model.json'
    data = json.loads(path.read_text())
    cells = [(r, c) for r in range(10) for c in range(-r, r+1)]
    indices = {position:i for i,position in enumerate(cells)}
    windows = [(indices[r-1,c], indices[r,c-1], indices[r,c], indices[r,c+1])
               for r in range(1, 10) for c in range(1-r, r)]
    assert len(windows) == len(set(windows)) == 81
    order = data['original_cell_order']
    assert sorted(order) == list(range(100))
    free = data['free_prefix_variables']
    pivots = data['eliminated_prefix_variables']
    assert free == [i for i in range(100) if i not in pivots] and len(free) == 96
    position = {global_index:i for i,global_index in enumerate(free)}
    y = {global_index:{1 << (4*i):1} for global_index,i in position.items()}
    for pivot in pivots:
        y[pivot] = {1 << (4*position[int(k)]):c
                    for k,c in data['prefix_variable_substitutions'][str(pivot)].items()}
    forms = {cell:add(y[j], y.get(j-1, {}), -1) for j,cell in enumerate(order)}
    for cell, form in forms.items():
        declared = {1 << (4*int(i)):c for i,c in data['original_color_linear_forms'][str(cell)].items()}
        assert declared == form
    prefix = {}
    for j,cell in enumerate(order):
        prefix = add(prefix, forms[cell])
        assert prefix == y[j]
    unary = []
    for role in range(4):
        total = {}
        for window in windows:
            total = add(total, forms[window[role]])
        assert not total
        coefficients = [0]*100
        for window in windows:
            j = order.index(window[role])
            coefficients[j] = (coefficients[j]+1) % 3
            if j:
                coefficients[j-1] = (coefficients[j-1]-1) % 3
        unary.append(coefficients)
    rank = 0
    for column in range(100):
        pivot_row = next((r for r in range(rank, 4) if unary[r][column]), None)
        if pivot_row is None:
            continue
        unary[rank], unary[pivot_row] = unary[pivot_row], unary[rank]
        inv = unary[rank][column]
        unary[rank] = [v*inv % 3 for v in unary[rank]]
        for r in range(4):
            if r != rank and unary[r][column]:
                coefficient = unary[r][column]
                unary[r] = [(a-coefficient*b) % 3 for a,b in zip(unary[r], unary[rank])]
        rank += 1
    assert rank == 4
    assert len(data['domain_equations']) == 96
    for i, equation in enumerate(data['domain_equations']):
        assert decode(equation) == {1 << (4*i):2, 3 << (4*i):1}
    declared = {e['label']:e for e in data['moment_equations']}
    assert len(declared) == 76
    powers = {cell:({0:1}, form, multiply(form, form)) for cell,form in forms.items()}
    vanished, total_terms = [], 0
    for exponents in itertools.product(range(3), repeat=4):
        if not any(exponents):
            continue
        actual = {}
        for window in windows:
            product = {0:1}
            for cell, exponent in zip(window, exponents):
                product = multiply(product, powers[cell][exponent])
            actual = add(actual, product)
        if exponents == (2, 2, 2, 2):
            actual = add(actual, {0:1}, -1)
        label = 'moment:'+','.join(map(str, exponents))
        if sum(exponents) == 1:
            assert not actual and label not in declared
            vanished.append(label)
        else:
            assert decode(declared[label]) == actual, label
            assert declared[label]['target_already_subtracted'] is True
            total_terms += len(actual)
    assert len(vanished) == 4 and total_terms == 96050
    from exact_msolve_backend import definitions, run
    source, metadata = definitions(prime=3, ternary_native_field=True)
    assert source == (HERE/'exact_f3_math_model.ms').read_text()
    directory = HERE/'exact_native_field_review_prepared'
    directory.mkdir(exist_ok=False)
    prepared = run(directory/'full', prime=3, ternary_native_field=True, prepare_only=True)
    assert (directory/'full.ms').read_text() == source
    assert prepared['count_divisor'] == prepared['count_multiplier'] == 1
    assert prepared['native_field_source_sha256'] == hashlib.sha256(path.read_bytes()).hexdigest()
    invalid = [dict(prime=2), dict(prefix='0'), dict(binary=True), dict(fixture='domain'),
               dict(pivot_order=True), dict(ternary_reduced='all'), dict(ternary_prefix_sums='all'),
               dict(histogram_e2=True), dict(histogram_e4=True), dict(prefix_field_equations=True)]
    for extra in invalid:
        kwargs = dict(prime=3, ternary_native_field=True)
        kwargs.update(extra)
        try:
            definitions(**kwargs)
        except ValueError:
            pass
        else:
            raise AssertionError(('invalid scope accepted', extra))
    report = dict(status='PASS', geometry='independent centered coordinates', windows=81,
                  coordinate_inverse_checks=100, unary_rank=rank, field_domains_checked=96,
                  moments_compared=76, vanished_moments=vanished, compared_moment_terms=total_terms,
                  source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  input_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  actual_prepare_only_status=prepared['status'], count_divisor=1,
                  rejected_incompatible_scopes=len(invalid), solver_calls=0,
                  full_count_status='NOT_COMPUTED')
    (HERE/'exact_native_field_review_results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
