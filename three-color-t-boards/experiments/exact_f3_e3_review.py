#!/usr/bin/env python3
"""Independent elementary-cubic certificate audit, with no solver invocation."""

import hashlib
import itertools
import json
from math import comb
from pathlib import Path

from exact_f3_review import add, decode, evaluate, multiply, reduce_fields

HERE = Path(__file__).resolve().parent


def elementary(forms):
    """Truncated product tree, independent of the owner's sequential update."""
    if not forms:
        return [{(): 1}, {}, {}, {}]
    if len(forms) == 1:
        return [{(): 1}, forms[0], {}, {}]
    split = len(forms) // 2
    a, b = elementary(forms[:split]), elementary(forms[split:])
    out = [{} for _ in range(4)]
    for degree in range(4):
        for k in range(degree + 1):
            out[degree] = add(out[degree], multiply(a[k], b[degree - k]))
    return out


def rank(polynomials):
    pivots = {}
    for polynomial in polynomials:
        row = dict(polynomial)
        while row:
            lead = min(row)
            if lead in pivots:
                row = add(row, pivots[lead], -row[lead])
            else:
                inverse = pow(row[lead], -1, 3)
                pivots[lead] = {term: c * inverse % 3 for term, c in row.items()}
                break
    return len(pivots)


def main():
    base_path = HERE / "exact_f3_math_model.json"
    path = HERE / "exact_f3_math_e3_constraints.json"
    base = json.loads(base_path.read_text())
    data = json.loads(path.read_text())
    assert (
        data["native_source_sha256"]
        == hashlib.sha256(base_path.read_bytes()).hexdigest()
    )
    assert (
        data["native_source_sha256"]
        == "fe1321842be3bf5bdb8ff91cd5b9c38017d542968fe27a8d5a8952e344564cc4"
    )
    assert data["free_prefix_variables"] == base["free_prefix_variables"]
    assert data["original_cell_order"] == base["original_cell_order"]
    windows = [
        ((r - 1) ** 2 + j - 1, r * r + j - 1, r * r + j, r * r + j + 1)
        for r in range(1, 10)
        for j in range(1, 2 * r)
    ]
    roles = {
        label: {w[k] for w in windows} for k, label in enumerate(("T", "L", "M", "R"))
    }
    forms = {
        int(cell): {(int(v),): c for v, c in linear.items()}
        for cell, linear in base["original_color_linear_forms"].items()
    }

    def sym(cells):
        return elementary([forms[cell] for cell in sorted(cells)])

    role_symmetric = {label: sym(cells) for label, cells in roles.items()}
    moments = decode(base["moment_equations"])
    for k, label in enumerate(("T", "L", "M", "R")):
        assert not role_symmetric[label][1]
        powersum = {}
        for cell in roles[label]:
            powersum = add(powersum, multiply(forms[cell], forms[cell]))
        exponents = tuple(2 if j == k else 0 for j in range(4))
        assert role_symmetric[label][2] == powersum
        assert (
            reduce_fields(powersum)
            == moments["moment:" + ",".join(map(str, exponents))]
        )
    expected = {"e3:T": role_symmetric["T"][3]}
    certificates = []
    for a, b in (("T", "M"), ("M", "L"), ("M", "R")):
        common = roles[a] & roles[b]
        left = roles[a] - roles[b]
        right = roles[b] - roles[a]
        C, D, E = sym(common), sym(left), sym(right)
        assert D[1] == E[1] == add({}, C[1], -1)
        difference = add(D[3], E[3], -1)
        lhs = add(add(role_symmetric[a][3], role_symmetric[b][3], -1), difference, -1)
        rhs = multiply(C[1], add(role_symmetric[a][2], role_symmetric[b][2], -1))
        assert lhs == rhs
        expected[f"e3:{a}:{b}"] = difference
        certificates.append({"roles": [a, b], "ordinary_correction_terms": len(rhs)})
    actual = decode(data["equations"])
    assert actual == {label: reduce_fields(poly) for label, poly in expected.items()}
    assert actual == expected  # Here every exported term is already a pure cubic.
    assert [len(p) for p in actual.values()] == [158, 180, 86, 150]
    assert all(len(term) == 3 for poly in actual.values() for term in poly)
    free = base["free_prefix_variables"]
    indices = {v: i for i, v in enumerate(free)}
    replacements = {
        int(p): {int(v): c for v, c in row.items()}
        for p, row in base["prefix_variable_substitutions"].items()
    }
    ys = [
        {(indices[v],): c for v, c in replacements.get(i, {i: 1}).items()}
        for i in range(100)
    ]
    path_polynomial = {}
    for a, b in itertools.pairwise(ys):
        path_polynomial = add(path_polynomial, multiply(multiply(a, a), b))
        path_polynomial = add(path_polynomial, multiply(a, multiply(b, b)), -1)
    assert path_polynomial == actual["e3:T"]
    before = [p for p in moments.values() if max(map(len, p)) <= 3]
    assert len(before) == 26
    ranks = [rank(before), rank(before + list(actual.values()))]
    assert ranks == [26, 30]
    survivor_counts = [0, 0]
    cases = 0
    for n0 in range(82):
        for n1 in range(82 - n0):
            n2 = 81 - n0 - n1
            histogram = (n0, n1, n2)
            cases += 1
            coefficients = [
                sum(
                    comb(n1, j) * comb(n2, k - j) * (-1) ** (k - j)
                    for j in range(k + 1)
                    if j <= n1 and k - j <= n2
                )
                % 3
                for k in range(1, 4)
            ]
            low = coefficients[:2] == [0, 0]
            high = low and coefficients[2] == 0
            assert low == all(n % 3 == 0 for n in histogram)
            assert high == (
                all(n % 3 == 0 for n in histogram)
                and len({n % 9 for n in histogram}) == 1
            )
            survivor_counts[0] += low
            survivor_counts[1] += high
    assert cases == 3403 and survivor_counts == [406, 136]
    witnesses = json.loads(
        (HERE / "exact_structure_gauge_certificate.json").read_text()
    )["boards"]
    for witness in witnesses:
        board = list(map(int, witness["flat"]))
        prefix = []
        value = 0
        for cell in base["original_cell_order"]:
            value = (value + board[cell]) % 3
            prefix.append(value)
        values = [prefix[v] for v in free]
        assert all(evaluate(poly, values) == 0 for poly in actual.values())
    report = {
        "status": "PASS",
        "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "native_source_sha256": data["native_source_sha256"],
        "ordinary_difference_certificates": certificates,
        "role_quadratic_power_sum_identities": 4,
        "top_path_identity": True,
        "exported_terms": [len(p) for p in actual.values()],
        "total_exported_terms": 574,
        "all_exported_terms_pure_cubic": True,
        "linear_span_ranks": ranks,
        "histogram_cases": cases,
        "histogram_survivors": survivor_counts,
        "existing_valid_witnesses_checked": len(witnesses),
        "solver_runs": 0,
        "count_preservation": "finite-field domain quotient is a product of F3 fields; valid-point vanishing implies ideal membership",
        "count_divisor": 1,
        "count_multiplier": 1,
        "full_count_status": "NOT_COMPUTED",
    }
    (HERE / "exact_f3_e3_review_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
