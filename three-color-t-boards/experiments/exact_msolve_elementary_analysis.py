#!/usr/bin/env python3
"""Bounded algebra/input diagnostics only; never invokes a polynomial solver.

All transformed arithmetic is ORDINARY F2 polynomial arithmetic. Nibbles
store exponents without reduction; transformed variables may vanish.
"""

import hashlib
import json
import random
from collections import Counter, defaultdict
from itertools import pairwise, product
from pathlib import Path
from typing import Any

from exact_parity_math_elementary import geometry

ROOT = Path(__file__).resolve().parent
MUL = ((0, 0, 0, 0), (0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2))
SIG_ORDER = [
    "1001",
    "1000",
    "1010",
    "1011",
    "1111",
    "1110",
    "1100",
    "0100",
    "0110",
    "0111",
    "0011",
    "0001",
]


def xor_into(target, source):
    target.symmetric_difference_update(source)


def multiply(a, b):
    out = set()
    for x in a:
        for y in b:
            z = x + y  # total degree <=8: no exponent nibble can overflow
            if z in out:
                out.remove(z)
            else:
                out.add(z)
    return out


def powers(monomial):
    while monomial:
        bit = (monomial & -monomial).bit_length() - 1
        variable = bit // 4
        exponent = (monomial >> (4 * variable)) & 15
        yield variable, exponent
        monomial &= ~(15 << (4 * variable))


def degree(monomial):
    return sum(e for _, e in powers(monomial))


def drl(monomial, n):
    return degree(monomial), tuple(
        -((monomial >> (4 * i)) & 15) for i in reversed(range(n))
    )


def evaluate(polynomial, values):
    total = 0
    for term in polynomial:
        value = 1
        for i, exponent in powers(term):
            for _ in range(exponent):
                value = MUL[value][values[i]]
        total ^= value
    return total


def make_forms(order, pivots, unary):
    substitutions = {
        p: sorted(row - {p}) for p, row in zip(pivots, unary, strict=False)
    }
    assert all(not set(v) & set(pivots) for v in substitutions.values())
    yforms = [set(substitutions.get(i, [i])) for i in range(100)]
    forms = {}
    for i, cell in enumerate(order):
        forms[cell] = yforms[i] ^ (yforms[i - 1] if i else set())
    assert all(forms.values()), "a color would be forced to zero"
    return substitutions, forms


def input_model(order, pivots, unary, windows, roles):
    substitutions, forms = make_forms(order, pivots, unary)
    free = [i for i in range(100) if i not in pivots]
    index = {v: i for i, v in enumerate(free)}
    linear = {
        cell: {1 << (4 * index[v]) for v in support} for cell, support in forms.items()
    }
    square = {cell: {2 * t for t in poly} for cell, poly in linear.items()}
    domains = [
        ("domain:" + str(cell), multiply(linear[cell], square[cell]) ^ {0})
        for cell in range(100)
    ]
    moments = []
    vanished = []
    for exponents in product(range(3), repeat=4):
        if not any(exponents):
            continue
        out = set()
        for window in windows:
            poly = {0}
            for cell, exponent in zip(window, exponents, strict=False):
                if exponent:
                    poly = multiply(
                        poly, linear[cell] if exponent == 1 else square[cell]
                    )
            xor_into(out, poly)
        label = "moment:" + ",".join(map(str, exponents))
        (moments if out else vanished).append((label, out))
    assert len(vanished) == 8
    # Elementary polynomials by a linear-time symmetric-sum recurrence.
    role_e2 = {}
    for role, cells in roles.items():
        e1, e2 = set(), set()
        for cell in sorted(cells):
            xor_into(e2, multiply(e1, linear[cell]))
            xor_into(e1, linear[cell])
        assert not e1
        role_e2[role] = e2
    elementary = [
        ("e2:T", role_e2["T"]),
        ("e2:T:M", role_e2["T"] ^ role_e2["M"]),
        ("e2:M:L", role_e2["M"] ^ role_e2["L"]),
        ("e2:M:R", role_e2["M"] ^ role_e2["R"]),
    ]
    # Ordinary squares are valid consequences; do not reduce exponent4 to1.
    elementary += [(name + ":square", {2 * t for t in p}) for name, p in elementary]
    return free, substitutions, forms, domains, moments, elementary


def describe(polys, n=96):
    unique = set().union(*(p for _, p in polys))
    leads = [max(p, key=lambda t: drl(t, n)) for _, p in polys if p]

    def support(p):
        return {i for t in p for i, e in powers(t)}

    return {
        "generators": len(polys),
        "total_terms": sum(len(p) for _, p in polys),
        "distinct_monomials": len(unique),
        "largest_polynomial_terms": max(len(x[1]) for x in polys),
        "max_total_degree": max(map(degree, unique)),
        "term_degree_histogram": dict(
            sorted(Counter(degree(t) for _, p in polys for t in p).items())
        ),
        "polynomial_degree_histogram": dict(
            sorted(Counter(max(map(degree, p)) for _, p in polys).items())
        ),
        "distinct_initial_leading_monomials": len(set(leads)),
        "linear_span_quadratic_rank": rank(
            [p for _, p in polys if max(map(degree, p)) <= 2]
        ),
        "details": [
            {
                "label": label,
                "terms": len(p),
                "variables": len(support(p)),
                "degree": max(map(degree, p)),
            }
            for label, p in polys
        ],
    }


def rank(polys):
    if not polys:
        return 0
    columns = {t: i for i, t in enumerate(set().union(*polys))}
    pivots = {}
    for p in polys:
        row = sum(1 << columns[t] for t in p)
        while row:
            lead = row.bit_length() - 1
            if lead in pivots:
                row ^= pivots[lead]
            else:
                pivots[lead] = row
                break
    return len(pivots)


def serialize(polys, n):
    def monomial(t):
        return (
            "*".join(f"x{i + 1}" + (f"^{e}" if e != 1 else "") for i, e in powers(t))
            or "1"
        )

    return (
        ",".join(f"x{i + 1}" for i in range(n))
        + "\n2\n"
        + ",\n".join("+".join(monomial(t) for t in sorted(p)) for _, p in polys)
        + "\n"
    )


def main():
    windows, roles = geometry()
    groups = defaultdict(list)
    for cell in range(100):
        signature = "".join(str(int(cell in cells)) for cells in roles.values())
        groups[signature].append(cell)
    assert set(SIG_ORDER) == set(groups)
    assert all(
        sum(a != b for a, b in zip(x, y, strict=False)) == 1
        for x, y in pairwise(SIG_ORDER)
    )
    order = [cell for sig in SIG_ORDER for cell in groups[sig]]
    assert set(order[:81]) == roles["T"]
    unary = []
    for cells in roles.values():
        row = set()
        for i, cell in enumerate(order):
            if cell in cells:
                xor_into(row, {i})
                if i:
                    xor_into(row, {i - 1})
        unary.append(row)
    assert [len(r) for r in unary] == [1, 2, 4, 5]
    assert sum(map(len, unary)) == len(set.union(*unary))
    candidates = []
    for pivots in product(*[sorted(row) for row in unary]):
        substitutions, forms = make_forms(order, pivots, unary)
        lengths = {cell: len(p) for cell, p in forms.items()}
        raw_moment_expansion = sum(
            __import__("math").prod(1 + 2 * lengths[cell] for cell in w) - 1
            for w in windows
        )
        candidates.append(
            {
                "pivots": list(pivots),
                "raw_all80_moment_expansion_terms": raw_moment_expansion,
                "domain_terms": sum(k * k + 1 for k in lengths.values()),
                "maximum_color_form_terms": max(lengths.values()),
            }
        )
    candidates.sort(
        key=lambda x: (
            x["raw_all80_moment_expansion_terms"],
            x["domain_terms"],
            x["pivots"],
        )
    )
    best = candidates[0]
    free, substitutions, forms, domains, moments, elementary = input_model(
        order, best["pivots"], unary, windows, roles
    )
    checks = 0
    rng = random.Random(314159)
    for _ in range(25):
        partial = [rng.randrange(4) for _ in free]
        y = [0] * 100
        for variable, value in zip(free, partial, strict=False):
            y[variable] = value
        for variable, source in substitutions.items():
            for j in source:
                y[variable] ^= y[j]
        z = [0] * 100
        for i, cell in enumerate(order):
            z[cell] = y[i] ^ (y[i - 1] if i else 0)
        # This validation permits zero values and does not use a cubic quotient.
        assert all(
            __import__("functools").reduce(int.__xor__, (z[c] for c in cells)) == 0
            for cells in roles.values()
        )
        for label, p in domains:
            cell = int(label.split(":")[1])
            assert evaluate(p, partial) == (MUL[z[cell]][MUL[z[cell]][z[cell]]] ^ 1)
            checks += 1
        for label, p in moments:
            exponents = list(map(int, label.split(":")[1].split(",")))
            direct = 0
            for w in windows:
                value = 1
                for cell, e in zip(w, exponents, strict=False):
                    for _ in range(e):
                        value = MUL[value][z[cell]]
                direct ^= value
            assert direct == evaluate(p, partial)
            checks += 1
        for label, p in elementary[:4]:
            evaluated = {}
            for role, cells in roles.items():
                a = b = 0
                for c in cells:
                    b ^= MUL[a][z[c]]
                    a ^= z[c]
                evaluated[role] = b
            tags = label.split(":")[1:]
            direct = 0
            for role in tags:
                direct ^= evaluated[role]
            assert direct == evaluate(p, partial)
            checks += 1
    # Export an UNEVALUATED candidate input for independent audit, never solve it.
    text = serialize(domains + moments, 96)
    path = ROOT / "exact_msolve_elementary_analysis_prefix_gray.ms"
    path.write_text(text)
    # Frozen, explicit coefficient-one polynomials for the backend adapter.
    # The nibble encoding is ordinary: e.g. exponent4 remains4.
    field_equations = [
        ("prefix_field:" + str(v), {1 << (4 * i), 4 << (4 * i)})
        for i, v in enumerate(free)
    ]

    def encode(polys):
        return [
            {"label": label, "terms": [hex(t) for t in sorted(p)]} for label, p in polys
        ]

    model = {
        "format": "t-board-prefix-sum-f2-v1",
        "variables": 96,
        "coefficient_characteristic": 2,
        "ring_type": "ordinary polynomial ring",
        "scope": "full labeled ternary boards",
        "standard_basis_complete": False,
        "status": "UNEVALUATED_GENERATING_IDEAL",
        "count_divisor": 1,
        "count_multiplier": 1,
        "symmetry_normalization": False,
        "original_cell_order": order,
        "signature_group_order": SIG_ORDER,
        "signature_group_sizes": {s: len(groups[s]) for s in SIG_ORDER},
        "forward_map": "y_j = sum_{k=0}^j z_order[k] in F2",
        "inverse_map": "z_order[j] = y_j + y_(j-1), with y_(-1)=0",
        "unary_supports": [sorted(r) for r in unary],
        "eliminated_prefix_variables": best["pivots"],
        "prefix_variable_substitutions": substitutions,
        "free_prefix_variables": free,
        "original_color_linear_forms": {str(k): sorted(v) for k, v in forms.items()},
        "monomial_encoding": "hex integer: exponent of free variable i in bits4*i..4*i+3; ordinary exponents, coefficient1",
        "domain_equations": encode(domains),
        "moment_equations": encode(moments),
        "elementary_equations": encode(elementary),
        "prefix_field_equations": encode(field_equations),
        "field_equation_identity": "y_j^4+y_j = sum_{k<=j} z_order[k]*(z_order[k]^3+1); substitute the four unary eliminations",
        "generator_source_sha256": hashlib.sha256(
            Path(__file__).read_bytes()
        ).hexdigest(),
    }
    model_path = ROOT / "exact_msolve_elementary_analysis_prefix_gray_model.json"
    model_path.write_text(json.dumps(model, indent=2) + "\n")
    report: dict[str, Any] = {
        "status": "ANALYSIS_ONLY_NO_SOLVER",
        "coordinate_change": "invertible prefix sums along signature Gray path",
        "original_cell_order": order,
        "signature_group_order": SIG_ORDER,
        "signature_group_sizes": {s: len(groups[s]) for s in SIG_ORDER},
        "unary_supports": [sorted(r) for r in unary],
        "eliminated_prefix_variables": best["pivots"],
        "prefix_variable_substitutions": substitutions,
        "free_prefix_variables": free,
        "color_form_sizes": dict(sorted(Counter(map(len, forms.values())).items())),
        "original_color_linear_forms": {str(k): sorted(v) for k, v in forms.items()},
        "scored_pivot_choices": candidates,
        "ordinary_polynomial_evaluation_checks": checks,
        "domain_statistics": describe(domains),
        "moment_statistics": describe(moments),
        "elementary_statistics": describe(elementary),
        "full_input_statistics": describe(domains + moments),
        "input_file": str(path),
        "input_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "input_bytes": len(text),
        "model_file": str(model_path),
        "model_sha256": hashlib.sha256(model_path.read_bytes()).hexdigest(),
        "input_scope": "unrestricted labeled count, divisor1 multiplier1; UNEVALUATED",
        "no_cubic_relations_on_individual_transformed_variables": True,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (ROOT / "exact_msolve_elementary_analysis.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(
        json.dumps(
            {
                k: v
                for k, v in report.items()
                if k
                not in (
                    "scored_pivot_choices",
                    "original_color_linear_forms",
                    "original_cell_order",
                )
                and not k.endswith("statistics")
            },
            indent=2,
        )
    )
    for key in [
        "domain_statistics",
        "moment_statistics",
        "elementary_statistics",
        "full_input_statistics",
    ]:
        print(key, json.dumps({k: v for k, v in report[key].items() if k != "details"}))


if __name__ == "__main__":
    main()
