#!/usr/bin/env python3
"""Deterministic graph-order study and pure renaming of frozen F3+e3 input.

No solver, new equations, prefix restriction, or change of counting scope.
The full polynomial-support graph and weaker monomial graph are distinguished.
"""

import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "exact_f3_translation_e3.ms"
SOURCE_SHA = "44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5"
MODEL = HERE / "exact_f3_translation_model.json"
MODEL_SHA = "1e2dc884f8996c6bd1b5093f24fa6fe7d7f1002e97b69762baadfda5adf94a7f"
E3 = HERE / "exact_f3_translation_e3_constraints.json"
E3_SHA = "5bed48f4a1523c26d02a2add9423c463ffdb08af5cf5ecf7bab40a0cceae4a40"
COUPLED = 95


def sha(data):
    return hashlib.sha256(data).hexdigest()


def bits(word):
    while word:
        low = word & -word
        yield low.bit_length() - 1
        word ^= low


def support(word):
    out = 0
    while word:
        i = ((word & -word).bit_length() - 1) // 4
        out |= 1 << i
        word &= ~(15 << (4 * i))
    return out


def add_clique(graph, vertices):
    for v in bits(vertices):
        graph[v] |= vertices ^ (1 << v)


def graphs(polynomials):
    primal = [0] * COUPLED
    monomial = [0] * COUPLED
    all_variable_labels = []
    for p in polynomials:
        polynomial_support = 0
        for coefficient, encoded in p["terms"]:
            assert coefficient in (1, 2)
            s = support(int(encoded, 16))
            if s >> COUPLED:
                assert s == 1 << COUPLED and p["label"] == "field:95"
                continue
            polynomial_support |= s
            add_clique(monomial, s)
        add_clique(primal, polynomial_support)
        if polynomial_support.bit_count() == COUPLED:
            all_variable_labels.append(p["label"])
    assert sum(v.bit_count() for v in primal) // 2 == 4465
    assert sum(v.bit_count() for v in monomial) // 2 == 868
    assert all_variable_labels
    return primal, monomial, all_variable_labels


def score(graph, remaining, v):
    neighbors = graph[v] & remaining
    degree = neighbors.bit_count()
    edge_count = sum((graph[w] & neighbors).bit_count() for w in bits(neighbors)) // 2
    return degree, degree * (degree - 1) // 2 - edge_count, neighbors


def eliminate(graph, policy):
    graph = graph.copy()
    remaining = (1 << COUPLED) - 1
    order = []
    degrees = []
    added = []
    while remaining:
        if policy == "natural":
            v = min(bits(remaining))
        elif policy == "reverse":
            v = max(bits(remaining))
        else:
            candidates = []
            for v in bits(remaining):
                degree, fill, _ = score(graph, remaining, v)
                key = (
                    (fill, degree, v) if policy == "minimum_fill" else (degree, fill, v)
                )
                candidates.append((key, v))
            v = min(candidates)[1]
        degree, fill, neighbors = score(graph, remaining, v)
        order.append(v)
        degrees.append(degree)
        added.append(fill)
        add_clique(graph, neighbors)
        remaining ^= 1 << v
    assert sorted(order) == list(range(COUPLED))
    return {
        "policy": policy,
        "elimination_order": order,
        "induced_width": max(degrees),
        "added_fill_edges": sum(added),
        "elimination_degrees": degrees,
        "fill_edges_by_step": added,
        "sum_elimination_degrees": sum(degrees),
    }


def parse_polynomials(text):
    lines = text.splitlines()
    assert lines[0] == ",".join(f"x{i + 1}" for i in range(96)) and lines[1] == "3"
    polys = []
    for expression in "\n".join(lines[2:]).strip().split(",\n"):
        p = {}
        for summand in expression.split("+"):
            factors = summand.split("*")
            coefficient = 1
            word = 0
            for factor in factors:
                if factor in ("1", "2"):
                    coefficient = coefficient * int(factor) % 3
                else:
                    match = re.fullmatch(r"x([1-9][0-9]*)(?:\^([1-9][0-9]*))?", factor)
                    assert match
                    v = int(match[1]) - 1
                    e = int(match[2] or 1)
                    assert 0 <= v < 96 and 1 <= e < 16 and not word >> (4 * v) & 15
                    word |= e << (4 * v)
            coefficient = (p.get(word, 0) + coefficient) % 3
            if coefficient:
                p[word] = coefficient
            elif word in p:
                del p[word]
        polys.append(p)
    return polys


def rename_source(source, old_to_new):
    head, prime, body = source.split("\n", 2)
    assert prime == "3"
    renamed = re.sub(
        r"\bx([1-9][0-9]*)\b", lambda m: f"x{old_to_new[int(m[1]) - 1] + 1}", body
    )
    return head + "\n" + prime + "\n" + renamed


def remap_word(word, old_to_new):
    result = 0
    while word:
        old = ((word & -word).bit_length() - 1) // 4
        exponent = word >> (4 * old) & 15
        result |= exponent << (4 * old_to_new[old])
        word &= ~(15 << (4 * old))
    return result


def build():
    source = SOURCE.read_bytes()
    model_raw = MODEL.read_bytes()
    e3_raw = E3.read_bytes()
    assert (
        sha(source) == SOURCE_SHA
        and sha(model_raw) == MODEL_SHA
        and sha(e3_raw) == E3_SHA
    )
    model = json.loads(model_raw)
    e3 = json.loads(e3_raw)
    polynomials = (
        model["domain_equations"] + model["moment_equations"] + e3["equations"]
    )
    assert len(polynomials) == 176
    actual = parse_polynomials(source.decode())
    expected = [{int(t, 16): c for c, t in p["terms"]} for p in polynomials]
    assert actual == expected
    primal, monomial, clique_labels = graphs(polynomials)
    policies = ("natural", "reverse", "minimum_fill", "minimum_degree")
    primal_results = [eliminate(primal, p) for p in policies]
    assert all(
        r["induced_width"] == 94 and r["added_fill_edges"] == 0 for r in primal_results
    )
    results = [eliminate(monomial, p) for p in policies]

    def metric(r):
        return (
            r["induced_width"],
            r["added_fill_edges"],
            r["sum_elimination_degrees"],
        )

    baseline = min(results[:2], key=metric)
    chosen = min(results[2:], key=lambda r: (metric(r), r["policy"]))
    improves = metric(chosen) < metric(baseline)
    audit = {
        "status": "PASS",
        "scope": "graph metrics and pure variable renaming; no solver",
        "source_file": SOURCE.name,
        "source_sha256": SOURCE_SHA,
        "variables": 96,
        "coupled_variables": 95,
        "independent_offset_index": 95,
        "full_polynomial_support_graph": {
            "edges": 4465,
            "complete": True,
            "clique_witness_labels": clique_labels,
            "every_order_width": 94,
            "every_order_fill": 0,
        },
        "monomial_cooccurrence_graph": {
            "edges": 868,
            "adjacency_hex": [hex(v) for v in monomial],
            "initial_degree_sequence": [v.bit_count() for v in monomial],
        },
        "monomial_graph_order_results": results,
        "metric_priority": [
            "induced_width",
            "added_fill_edges",
            "sum_elimination_degrees",
        ],
        "best_baseline_policy": baseline["policy"],
        "selected_policy": chosen["policy"] if improves else None,
        "improves_best_baseline": improves,
        "limitation": "monomial graph omits co-occurrence across different terms of a global equation; its width is not a treewidth bound for the full polynomial factor graph or a Groebner runtime bound",
        "full_count_status": "UNEVALUATED",
    }
    files = []
    if improves:
        new_to_old = chosen["elimination_order"] + [95]
        old_to_new = [0] * 96
        for new, old in enumerate(new_to_old):
            old_to_new[old] = new
        assert new_to_old[95] == old_to_new[95] == 95
        renamed = rename_source(source.decode(), old_to_new)
        assert rename_source(renamed, new_to_old) == source.decode()
        parsed = parse_polynomials(renamed)
        assert len(parsed) == 176
        for original, changed in zip(actual, parsed, strict=False):
            assert changed == {
                remap_word(t, old_to_new): c for t, c in original.items()
            }
        _new_primal, new_monomial, _ = graphs(
            [
                {
                    "label": p["label"],
                    "terms": [[c, hex(t)] for t, c in changed.items()],
                }
                for p, changed in zip(polynomials, parsed, strict=False)
            ]
        )
        assert (
            eliminate(new_monomial, "natural")["induced_width"]
            == chosen["induced_width"]
        )
        assert (
            eliminate(new_monomial, "natural")["added_fill_edges"]
            == chosen["added_fill_edges"]
        )
        mapping = {
            "format": "t-board-f3-variable-order-v1",
            "coefficient_characteristic": 3,
            "variables": 96,
            "generators": 176,
            "scope": "full labeled ternary boards",
            "source_file": SOURCE.name,
            "source_sha256": SOURCE_SHA,
            "source_translation_model_sha256": MODEL_SHA,
            "source_e3_sha256": E3_SHA,
            "renamed_file": "exact_f3_order_selected.ms",
            "renamed_sha256": sha(renamed.encode()),
            "policy": chosen["policy"],
            "order_semantics": "new variable position lists the old variable eliminated next by the graph heuristic",
            "new_index_to_old_index": new_to_old,
            "old_index_to_new_index": old_to_new,
            "new_variable_coordinates": [
                {
                    "new_index": new,
                    "old_index": old,
                    "normalized_prefix_index": model[
                        "free_normalized_prefix_variables"
                    ][old],
                }
                if old < 95
                else {
                    "new_index": 95,
                    "old_index": 95,
                    "coordinate": "independent original apex offset a",
                }
                for new, old in enumerate(new_to_old)
            ],
            "original_color_linear_forms_in_new_variables": {
                cell: {str(old_to_new[int(v)]): c for v, c in form.items()}
                for cell, form in model["original_color_linear_forms"].items()
            },
            "offset_variable_index": 95,
            "count_divisor": 1,
            "count_multiplier": 1,
            "prefix": "",
            "fixed_original_cells": [],
            "symmetry_normalization": False,
            "only_change": "bijective variable renaming; every polynomial, coefficient, domain, and generator order retained",
            "inverse_renaming_recovers_source_byte_for_byte": True,
            "all_polynomials_independently_parsed_and_permuted": True,
            "monomial_graph_metrics": {
                k: chosen[k]
                for k in (
                    "induced_width",
                    "added_fill_edges",
                    "sum_elimination_degrees",
                )
            },
            "status": "PREPARED_NOT_RUN",
            "full_count_status": "UNEVALUATED",
        }
        map_text = json.dumps(mapping, indent=2) + "\n"
        files = [
            ("exact_f3_order_selected.ms", renamed),
            ("exact_f3_order_selected.json", map_text),
        ]
        audit["exports"] = [
            {"file": name, "sha256": sha(text.encode())} for name, text in files
        ]
        audit["inverse_renaming_recovers_source_byte_for_byte"] = True
    return files, audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    files, audit = build()
    files.append(("exact_f3_order_audit.json", json.dumps(audit, indent=2) + "\n"))
    for name, text in files:
        path = HERE / name
        if args.check:
            assert path.read_text() == text
        else:
            path.write_text(text)
    print(
        json.dumps(
            {
                "status": audit["status"],
                "full_polynomial_graph_edges": 4465,
                "full_polynomial_graph_width": 94,
                "monomial_graph_edges": 868,
                "results": [
                    {
                        k: r[k]
                        for k in (
                            "policy",
                            "induced_width",
                            "added_fill_edges",
                            "sum_elimination_degrees",
                        )
                    }
                    for r in audit["monomial_graph_order_results"]
                ],
                "selected_policy": audit["selected_policy"],
                "exports": audit.get("exports", []),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
