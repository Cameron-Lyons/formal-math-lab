#!/usr/bin/env python3
"""Independent finite checks for the Möbius-arrangement report; stdlib only."""
import json
from math import comb
from pathlib import Path

from exact_mobius_small import cell_partition, compute, windows


EXPECTED = {
    1: {1: 1},
    2: {4: 1},
    3: {9: 1, 5: -6, 3: 2, 2: 9, 1: -6},
    4: {16: 1, 12: -36, 10: 19, 9: 88, 8: 374, 7: -220,
        6: -889, 5: 449, 4: -834, 3: 1426, 2: 400, 1: -778},
}


def trim(a):
    a = list(a)
    while a and not a[-1]:
        a.pop()
    return a


def remainder(a, b, p):
    a = trim([x % p for x in a]); b = trim([x % p for x in b])
    assert b
    while len(a) >= len(b):
        shift = len(a) - len(b)
        scale = a[-1] * pow(b[-1], -1, p) % p
        for i, x in enumerate(b):
            a[i + shift] = (a[i + shift] - scale * x) % p
        a = trim(a)
    return a


def multiply_mod(a, b, f, p):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] = (c[i + j] + x * y) % p
    return remainder(c, f, p)


def power_mod(a, exponent, f, p):
    out = [1]
    while exponent:
        if exponent & 1:
            out = multiply_mod(out, a, f, p)
        a = multiply_mod(a, a, f, p)
        exponent >>= 1
    return out


def gcd(a, b, p):
    while b:
        a, b = b, remainder(a, b, p)
    if not a:
        return []
    scale = pow(a[-1], -1, p)
    return [(x * scale) % p for x in a]


def subtract_x(a, p):
    out = list(a) + [0] * max(0, 2 - len(a))
    out[1] = (out[1] - 1) % p
    return trim(out)


def prime_divisors(n):
    return [d for d in range(2, n + 1)
            if n % d == 0 and all(d % k for k in range(2, d))]


def irreducible_certificate(f, p):
    """Rabin criterion: x^(p^n)=x; coprime at n/r for every prime r|n."""
    f = trim([x % p for x in f]); n = len(f) - 1
    powers = [[0, 1]]
    for _ in range(n):
        powers.append(power_mod(powers[-1], p, f, p))
    assert not subtract_x(powers[n], p)
    checks = {}
    for r in prime_divisors(n):
        g = gcd(f, subtract_x(powers[n // r], p), p)
        assert g == [1]
        checks[str(r)] = {'exponent_index': n // r, 'gcd': g}
    return {'prime': p, 'degree': n, 'coefficients_low_to_high': f,
            'frobenius_full_residue': powers[n], 'proper_degree_checks': checks}


def divide_q_qminus1(coefficients):
    degree = max(coefficients)
    # First divide by q; then synthetic division by q-1 over Z.
    assert coefficients.get(0, 0) == 0
    dividend = [coefficients.get(i + 1, 0) for i in range(degree)]
    quotient = [0] * (degree - 1)
    quotient[-1] = dividend[-1]
    for i in range(len(quotient) - 2, -1, -1):
        quotient[i] = dividend[i + 1] + quotient[i + 1]
    assert dividend[0] + quotient[0] == 0
    return quotient


def implies(cells, w, a, b):
    return all(cells[x] == cells[y] for x, y in zip(w[a], w[b]))


def main():
    report = {'small_polynomials': [], 'irreducibility': {}}
    for h in range(1, 5):
        data, _, _ = compute(h)
        assert data['coefficients'] == EXPECTED[h]
        data.pop('fiber_size_histogram')
        report['small_polynomials'].append(data)
        path = Path(__file__).with_name(f'exact_mobius_closure_h{h}.json')
        if path.exists():
            other = json.loads(path.read_text())
            assert other['status'] == 'COMPLETE'
            assert {int(k): v for k, v in other['coefficients'].items()} == EXPECTED[h]
            assert other['nonzero_closures'] == data['nonzero_mobius_closures']
    for h, p in [(3, 7), (4, 3)]:
        quotient = divide_q_qminus1(EXPECTED[h])
        report['irreducibility'][str(h)] = irreducible_certificate(quotient, p)

    # Closure exchange fails at height four. Window indices are row-major.
    w = windows(4); base = [list(range(7))]
    s = cell_partition(4, base)
    sa = cell_partition(4, base + [[0, 8]])
    sb = cell_partition(4, base + [[0, 7]])
    assert list(s) == [0] * 14 + [1, 2]
    assert not implies(s, w, 0, 7)
    assert implies(sa, w, 0, 7)
    assert not implies(sb, w, 0, 8)
    report['exchange_failure'] = {
        'base_placement_block': list(range(7)), 'a': [0, 8], 'b': [0, 7],
        'base_cell_classes': list(s), 'after_a': list(sa), 'after_b': list(sb),
    }

    # An induced packing gives a partition-lattice interval of nonzero weight.
    w = windows(10)
    selected = [((r - 1) ** 2 + j) for r in range(1, 10, 2)
                for j in range(0, 2 * r - 1, 3)]
    used = set()
    for i in selected:
        assert not used.intersection(w[i])
        used.update(w[i])
    assert len(selected) == 17
    assert all(not set(window).issubset(used) for i, window in enumerate(w)
               if i not in selected)
    # For each role, a cell appears in at most one window in that role.
    for role in range(4):
        assert len({window[role] for window in w}) == len(w)
    bell = [1]
    for n in range(17):
        bell.append(sum(comb(n, k) * bell[k] for k in range(n + 1)))
    assert bell[17] == 82864869804
    report['nonzero_closure_lower_bound_h10'] = {
        'selected_placements': selected, 'selected_windows': [w[i] for i in selected],
        'covered_cells': len(used), 'induced_packing_size': len(selected),
        'partition_lattice_size': bell[17],
    }
    # Identical abstract component shapes need different collision updates.
    first = cell_partition(10, [[64, 67]])
    second = cell_partition(10, [[0, 4]])
    first_after = cell_partition(10, [[64, 67], [65, 68]])
    second_after = cell_partition(10, [[0, 4], [65, 68]])
    shape = lambda state: sorted(state.count(i) for i in set(state))
    assert shape(first) == shape(second) == [1] * 92 + [2] * 4
    assert max(first) + 1 == max(second) + 1 == 96
    assert max(first_after) + 1 == 94
    assert max(second_after) + 1 == 92
    report['component_shape_update_obstruction'] = {
        'first_collision': [64, 67], 'second_collision': [0, 4],
        'next_collision': [65, 68], 'initial_classes': 96,
        'first_updated_classes': 94, 'second_updated_classes': 92,
        'initial_component_sizes': [1] * 92 + [2] * 4,
    }
    path = Path(__file__).with_name('exact_mobius_check_results.json')
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'output': str(path),
                      'h10_nonzero_closure_lower_bound': bell[17]}))


if __name__ == '__main__':
    main()
