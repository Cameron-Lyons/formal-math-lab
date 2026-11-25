#!/usr/bin/env python3
"""Independent permutation, polynomial, offset and graph-metric audit."""

import hashlib
import json
import re
from itertools import combinations
from pathlib import Path

from exact_f3_review import parse_input

HERE = Path(__file__).resolve().parent


def eliminate(adjacency, policy):
    graph = {i: set(neighbors) for i, neighbors in enumerate(adjacency)}
    order = []
    degrees = []
    fills = []
    while graph:

        def score(v):
            ns = graph[v]
            missing = sum(b not in graph[a] for a, b in combinations(sorted(ns), 2))
            return (
                (missing, len(ns), v)
                if policy == "minimum_fill"
                else (len(ns), missing, v)
            )

        if policy == "natural":
            chosen = min(graph)
        elif policy == "reverse":
            chosen = max(graph)
        else:
            chosen = min(graph, key=score)
        ns = graph[chosen]
        degrees.append(len(ns))
        fill = 0
        for a, b in combinations(sorted(ns), 2):
            if b not in graph[a]:
                graph[a].add(b)
                graph[b].add(a)
                fill += 1
        fills.append(fill)
        order.append(chosen)
        for v in ns:
            graph[v].remove(chosen)
        del graph[chosen]
    return {
        "elimination_order": order,
        "induced_width": max(degrees),
        "added_fill_edges": sum(fills),
        "elimination_degrees": degrees,
        "fill_edges_by_step": fills,
        "sum_elimination_degrees": sum(degrees),
    }


def main():
    mapping_path = HERE / "exact_f3_order_selected.json"
    mapping = json.loads(mapping_path.read_text())
    graph_audit = json.loads((HERE / "exact_f3_order_audit.json").read_text())
    original = (HERE / "exact_f3_translation_e3.ms").read_text()
    renamed = (HERE / "exact_f3_order_selected.ms").read_text()
    model = json.loads((HERE / "exact_f3_translation_model.json").read_text())
    assert hashlib.sha256(original.encode()).hexdigest() == mapping["source_sha256"]
    assert hashlib.sha256(renamed.encode()).hexdigest() == mapping["renamed_sha256"]
    old_to_new = mapping["old_index_to_new_index"]
    new_to_old = mapping["new_index_to_old_index"]
    assert sorted(old_to_new) == sorted(new_to_old) == list(range(96))
    assert all(new_to_old[old_to_new[i]] == i for i in range(96))
    assert old_to_new[95] == new_to_old[95] == mapping["offset_variable_index"] == 95
    before, after = parse_input(original), parse_input(renamed)
    assert len(before) == len(after) == mapping["generators"] == 176
    for a, b in zip(before, after, strict=False):
        changed = {
            tuple(sorted(old_to_new[i] for i in term)): c for term, c in a.items()
        }
        assert changed == b and len(a) == len(b)
        restored = {
            tuple(sorted(new_to_old[i] for i in term)): c for term, c in b.items()
        }
        assert restored == a
    lines = renamed.split("\n", 2)
    restored_body = re.sub(
        r"\bx([1-9][0-9]*)\b",
        lambda m: "x" + str(new_to_old[int(m[1]) - 1] + 1),
        lines[2],
    )
    assert lines[0] + "\n" + lines[1] + "\n" + restored_body == original
    assert before[95] == after[95] == {(95, 95, 95): 1, (95,): 2}
    assert sum(any(95 in term for term in p) for p in after) == 1
    for cell, form in model["original_color_linear_forms"].items():
        expected = {str(old_to_new[int(i)]): c for i, c in form.items()}
        assert mapping["original_color_linear_forms_in_new_variables"][cell] == expected
    for new, old in enumerate(new_to_old):
        item = mapping["new_variable_coordinates"][new]
        assert item["new_index"] == new and item["old_index"] == old
        if new < 95:
            assert (
                item["normalized_prefix_index"]
                == model["free_normalized_prefix_variables"][old]
            )
        else:
            assert item["coordinate"] == "independent original apex offset a"
    monomial = [set() for _ in range(95)]
    primal = [set() for _ in range(95)]
    for polynomial in before:
        support = set()
        for term in polynomial:
            vertices = set(term) - {95}
            support |= vertices
            for a, b in combinations(sorted(vertices), 2):
                monomial[a].add(b)
                monomial[b].add(a)
        for a, b in combinations(sorted(support), 2):
            primal[a].add(b)
            primal[b].add(a)
    assert all(ns == set(range(95)) - {i} for i, ns in enumerate(primal))
    assert sum(map(len, primal)) // 2 == 4465 and sum(map(len, monomial)) // 2 == 868
    assert [hex(sum(1 << v for v in ns)) for ns in monomial] == graph_audit[
        "monomial_cooccurrence_graph"
    ]["adjacency_hex"]
    metrics = {}
    for policy in ("natural", "reverse", "minimum_degree", "minimum_fill"):
        actual = eliminate(monomial, policy)
        saved = next(
            r
            for r in graph_audit["monomial_graph_order_results"]
            if r["policy"] == policy
        )
        assert all(actual[k] == saved[k] for k in actual)
        metrics[policy] = {
            k: actual[k]
            for k in ("induced_width", "added_fill_edges", "sum_elimination_degrees")
        }
        if policy == "minimum_fill":
            assert actual["elimination_order"] == new_to_old[:95]
    assert metrics["minimum_fill"] == mapping["monomial_graph_metrics"]
    assert mapping["count_divisor"] == mapping["count_multiplier"] == 1
    assert (
        mapping["prefix"] == ""
        and mapping["fixed_original_cells"] == []
        and mapping["symmetry_normalization"] is False
    )
    witnesses = json.loads(
        (HERE / "exact_structure_gauge_certificate.json").read_text()
    )["boards"]
    for entry in witnesses:
        board = list(map(int, entry["flat"]))
        offset = board[0]
        prefix = []
        value = 0
        for cell in model["original_cell_order"]:
            value = (value + board[cell] - offset) % 3
            prefix.append(value)
        old_values = [prefix[j] for j in model["free_normalized_prefix_variables"]] + [
            offset
        ]
        new_values = [old_values[old] for old in new_to_old]
        assert [new_values[old_to_new[i]] for i in range(96)] == old_values
        for cell, form in mapping[
            "original_color_linear_forms_in_new_variables"
        ].items():
            assert (
                sum(c * new_values[int(v)] for v, c in form.items()) % 3
                == board[int(cell)]
            )
    result = {
        "status": "PASS",
        "mapping_sha256": hashlib.sha256(mapping_path.read_bytes()).hexdigest(),
        "input_sha256": mapping["renamed_sha256"],
        "source_input_sha256": mapping["source_sha256"],
        "complete_polynomials_compared": 176,
        "coefficient_terms_compared": sum(map(len, before)),
        "inverse_text_roundtrip": True,
        "offset_remains_index95_and_own_field_domain": True,
        "original_color_maps_compared": 100,
        "witness_coordinate_roundtrips": len(witnesses),
        "polynomial_support_graph": {
            "vertices": 95,
            "edges": 4465,
            "complete": True,
            "all_order_width": 94,
        },
        "monomial_cooccurrence_edges": 868,
        "independently_checked_metrics": metrics,
        "limitation": "monomial graph ignores coupling across terms in a generator; no full factor-graph width or solver speed bound follows",
        "count_divisor": 1,
        "count_multiplier": 1,
        "solver_runs": 0,
        "full_count_status": "NOT_COMPUTED",
    }
    (HERE / "exact_f3_order_review_results.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
