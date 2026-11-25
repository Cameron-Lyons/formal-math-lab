#!/usr/bin/env python3
"""Independent audit of the adapter's pure variable permutation; no solver."""

import hashlib
import json
import re
from collections import Counter
from itertools import product
from pathlib import Path

import exact_msolve_backend as adapter

HERE = Path(__file__).resolve().parent
CELLS = {(r, x): r * r + r + x for r in range(10) for x in range(-r, r + 1)}
WINDOWS = [
    (CELLS[r, x], CELLS[r + 1, x - 1], CELLS[r + 1, x], CELLS[r + 1, x + 1])
    for r in range(9)
    for x in range(-r, r + 1)
]
EXPONENTS = [e for e in product(range(3), repeat=4) if any(e)]


def expected_equations(p, prefix):
    equations = []
    for e in EXPONENTS:
        terms = Counter()
        for window in WINDOWS:
            power = (
                sum(
                    int(prefix[cell]) * exponent
                    for cell, exponent in zip(window, e, strict=False)
                    if cell < len(prefix)
                )
                % 3
            )
            pairs = tuple(
                sorted(
                    (cell, exponent)
                    for cell, exponent in zip(window, e, strict=False)
                    if cell >= len(prefix) and exponent
                )
            )
            u, v = ((1, 0), (0, 1), (p - 1, p - 1))[power]
            terms[pairs] += u
            if v:
                terms[tuple(sorted((*pairs, (100, 1))))] += v
        reduced = {
            term: coefficient % p
            for term, coefficient in terms.items()
            if coefficient % p
        }
        if reduced:
            equations.append(reduced)
    return equations


def parse(text, metadata):
    p = metadata["prime"]
    n = metadata["variables"]
    free = metadata["free_board_variables"]
    original = metadata["variable_original_cells"]
    assert len(original) == len(set(original)) == free
    assert sorted(original) == list(range(len(metadata["prefix"]), 100))
    lines = text.splitlines()
    assert lines[0] == ",".join(f"x{i + 1}" for i in range(n)) and lines[1] == str(p)
    polys = "\n".join(lines[2:]).strip().split(",\n")
    assert len(polys) == metadata["generators"]
    assert polys[:free] == [f"x{i + 1}^3-1" for i in range(free)]
    start = free
    if metadata["extension_variable"]:
        assert n == free + 1
        assert polys[start] == f"x{free + 1}^2+x{free + 1}+1"
        start += 1
    else:
        assert n == free
    equations = []
    for expression in polys[start:]:
        terms = Counter()
        for summand in expression.split("+"):
            factors = summand.split("*")
            coefficient = int(factors.pop(0))
            pairs = []
            assert 0 < coefficient < p
            for factor in factors:
                match = re.fullmatch(r"x([1-9][0-9]*)(?:\^([12]))?", factor)
                assert match, factor
                variable = int(match[1]) - 1
                assert 0 <= variable < n
                cell = original[variable] if variable < free else 100
                if cell == 100:
                    assert variable == n - 1 and metadata["extension_variable"]
                pairs.append((cell, int(match[2] or 1)))
            assert len({cell for cell, _ in pairs}) == len(pairs)
            terms[tuple(sorted(pairs))] += coefficient
        equations.append(
            {
                term: coefficient % p
                for term, coefficient in terms.items()
                if coefficient % p
            }
        )
    return equations


def unary_pivots(order, p):
    rows = []
    for role in range(4):
        present = {w[role] for w in WINDOWS}
        rows.append([int(cell in present) for cell in order])
    rank = 0
    pivots = []
    for column in range(len(order)):
        pivot = next((r for r in range(rank, 4) if rows[r][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = pow(rows[rank][column], -1, p)
        rows[rank] = [(a * inverse) % p for a in rows[rank]]
        for r in range(4):
            if r != rank:
                scalar = rows[r][column]
                rows[r] = [
                    (a - scalar * b) % p
                    for a, b in zip(rows[r], rows[rank], strict=False)
                ]
        pivots.append(order[column])
        rank += 1
        if rank == 4:
            break
    assert rank == 4
    return pivots


def main():
    reports = []
    for p in (2, 29):
        for prefix in ("", "0012"):
            natural, natural_meta = adapter.definitions(
                p, prefix=prefix, pivot_order=False
            )
            reordered, metadata = adapter.definitions(
                p, prefix=prefix, pivot_order=True
            )
            expected_order = [c for c in (0, 81, 90, 99) if c >= len(prefix)]
            expected_order += [
                c for c in range(len(prefix), 100) if c not in expected_order
            ]
            assert metadata["variable_original_cells"] == expected_order
            assert metadata["dispersed_variable_order"] is True
            assert natural_meta["model_data_sha256"] == metadata["model_data_sha256"]
            expected = expected_equations(p, prefix)
            assert parse(natural, natural_meta) == expected
            assert parse(reordered, metadata) == expected
            assert len(expected) == 80
            tag = f"p{p}" + ("_prefix0012" if prefix else "_full")
            path = HERE / f"exact_parity_math_pivot_{tag}.ms"
            path.write_text(reordered)
            record = dict(
                metadata,
                status="PREPARED_ONLY_NO_SOLVER",
                input_sha256=hashlib.sha256(reordered.encode()).hexdigest(),
            )
            path.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")
            result = {
                "prime": p,
                "prefix": prefix,
                "variables": metadata["variables"],
                "free_board_variables": metadata["free_board_variables"],
                "generators": metadata["generators"],
                "ordinary_cubic_domains": 100 - len(prefix),
                "all80_moments_match_centered_geometry": True,
                "natural_and_reordered_polynomials_identical_after_inverse_renaming": True,
                "extension_variable": metadata["extension_variable"],
                "extension_variable_remains_last": True,
                "count_divisor_unchanged": metadata["count_divisor"]
                == natural_meta["count_divisor"],
                "first_original_cells": expected_order[:4],
                "input_file": path.name,
                "input_sha256": record["input_sha256"],
            }
            if not prefix:
                assert metadata["variables"] == 100 and metadata["generators"] == 180
                assert (
                    not metadata["extension_variable"]
                    and metadata["count_divisor"] == 1
                )
                assert metadata["scope"] == "full labeled boards"
                assert unary_pivots(list(range(100)), p) == [0, 1, 2, 3]
                assert unary_pivots(expected_order, p) == [0, 81, 90, 99]
                result.update(
                    natural_unary_pivots=[0, 1, 2, 3],
                    dispersed_unary_pivots=[0, 81, 90, 99],
                )
            else:
                assert metadata["extension_variable"] and metadata["variables"] == 97
                assert metadata["count_divisor"] == 2
            reports.append(result)
    assert max(len(set(w) & {0, 1, 2, 3}) for w in WINDOWS) == 4
    assert max(len(set(w) & {0, 81, 90, 99}) for w in WINDOWS) == 1
    report = {
        "status": "PASS",
        "solver_invoked": False,
        "full_count_evaluated": False,
        "adapter_sha256": hashlib.sha256(
            Path(adapter.__file__).read_bytes()
        ).hexdigest(),
        "cases": reports,
        "maximum_pivot_cells_per_T": {"natural": 4, "dispersed": 1},
    }
    (HERE / "exact_parity_math_pivot_audit.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
