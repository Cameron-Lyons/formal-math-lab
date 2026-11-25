#!/usr/bin/env python3
"""Independent full input audit of the prefix-sum coordinate model; no solver."""

import hashlib
import json
import random
from itertools import product
from pathlib import Path
from unittest.mock import patch

import exact_msolve_backend as backend
from exact_msolve_prefix_sums import prefix_definitions
from exact_pivot_review_common import (
    build_expected,
    decode_polynomials,
    evaluate,
    geometry,
    input_polynomials,
    multiply,
    solve_linears,
    square,
)

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "exact_msolve_elementary_analysis_prefix_gray_model.json"


def main():
    model = json.loads(SOURCE.read_text())
    assert model["count_divisor"] == model["count_multiplier"] == 1
    assert (
        model["symmetry_normalization"] is False
        and model["standard_basis_complete"] is False
    )
    assert model["coefficient_characteristic"] == 2 and model["variables"] == 96
    _windows, roles = geometry()
    order = model["original_cell_order"]
    assert len(order) == 100 and set(order) == set(range(100))
    groups = {signature: [] for signature in model["signature_group_order"]}
    for cell in range(100):
        signature = "".join(
            str(int(cell in roles[label])) for label in ("T", "L", "M", "R")
        )
        groups[signature].append(cell)
    assert order == [
        cell for group in model["signature_group_order"] for cell in groups[group]
    ]
    assert set(order[:81]) == roles["T"]
    # Explicitly compose both triangular maps on all100 basis vectors.
    for cell in range(100):
        original = [int(i == cell) for i in range(100)]
        prefix = []
        value = 0
        for source in order:
            value ^= original[source]
            prefix.append(value)
        recovered = [0] * 100
        for i, source in enumerate(order):
            recovered[source] = prefix[i] ^ (prefix[i - 1] if i else 0)
        assert recovered == original
    unary = []
    for cells in roles.values():
        row = set()
        for i, cell in enumerate(order):
            if cell in cells:
                row ^= {i}
                if i:
                    row ^= {i - 1}
        unary.append(row)
    assert [sorted(row) for row in unary] == model["unary_supports"]
    pivots = model["eliminated_prefix_variables"]
    replacements = solve_linears(unary, pivots)
    assert {str(k): sorted(v) for k, v in replacements.items()} == model[
        "prefix_variable_substitutions"
    ]
    free = [i for i in range(100) if i not in pivots]
    assert free == model["free_prefix_variables"]
    index = {v: i for i, v in enumerate(free)}
    yforms = [replacements.get(i, {i}) for i in range(100)]
    forms = {
        cell: yforms[i] ^ (yforms[i - 1] if i else set())
        for i, cell in enumerate(order)
    }
    assert all(forms.values())
    assert {str(k): sorted(v) for k, v in forms.items()} == model[
        "original_color_linear_forms"
    ]
    indexed = {cell: {index[v] for v in support} for cell, support in forms.items()}
    domains, moments, elementary, vanished = build_expected(indexed, False)
    actual_domains = decode_polynomials(model["domain_equations"], 96, 4, 8)
    actual_moments = decode_polynomials(model["moment_equations"], 96, 4, 8)
    actual_elementary = decode_polynomials(model["elementary_equations"], 96, 4, 8)
    assert (
        actual_domains == domains
        and actual_moments == moments
        and actual_elementary == elementary
    )
    fields = {f"prefix_field:{v}": {(i,), (i, i, i, i)} for i, v in enumerate(free)}
    assert decode_polynomials(model["prefix_field_equations"], 96, 4, 8) == fields
    # Polynomial ideal membership of every optional field equation, not only evaluation.
    zforms = {cell: {(i,) for i in support} for cell, support in indexed.items()}
    partial = set()
    for j, cell in enumerate(order):
        partial ^= multiply(zforms[cell], domains[f"domain:{cell}"])
        yf = {(index[v],) for v in yforms[j]}
        assert partial == square(square(yf)) ^ yf
    rng = random.Random(0xC001D1A7)
    for _ in range(20):
        values = [rng.randrange(4) for _ in free]
        ys = [0] * 100
        for variable, value in zip(free, values, strict=False):
            ys[variable] = value
        for variable, support in replacements.items():
            for source in support:
                ys[variable] ^= ys[source]
        zs = [0] * 100
        for j, cell in enumerate(order):
            zs[cell] = ys[j] ^ (ys[j - 1] if j else 0)
        assert all(evaluate(zforms[cell], values) == zs[cell] for cell in range(100))
    seeds = json.loads((HERE.parent / "sources/anc/certificates.json").read_text())[
        "ternary_seeds"
    ]
    witness_checks = []
    for rows in seeds:
        zs = [int(c) + 1 for c in "".join(rows)]
        ys = []
        value = 0
        for cell in order:
            value ^= zs[cell]
            ys.append(value)
        values = [ys[v] for v in free]
        assert all(
            ys[p]
            == __import__("functools").reduce(int.__xor__, (ys[v] for v in support), 0)
            for p, support in replacements.items()
        )
        assert all(
            evaluate(p, values) == 0
            for p in list(domains.values())
            + list(moments.values())
            + list(elementary.values())
            + list(fields.values())
        )
        witness_checks.append(
            {"zero_free_coordinates": sum(value == 0 for value in values)}
        )
    assert any(row["zero_free_coordinates"] for row in witness_checks)
    prepared = HERE / "exact_pivot_review_prefix_prepared"
    prepared.mkdir(exist_ok=False)
    variants = []
    for all_moments, histogram, field_equations in product((False, True), repeat=3):
        mode = "all" if all_moments else "representatives"
        name = f"{mode}_e{int(histogram)}_f{int(field_equations)}"
        selected = {
            label: p
            for label, p in moments.items()
            if all_moments
            or next(x for x in map(int, label.split(":")[1].split(",")) if x) == 1
        }
        wanted = list(domains.values()) + list(selected.values())
        if histogram:
            wanted += list(elementary.values())
        if field_equations:
            wanted += list(fields.values())
        text, metadata = prefix_definitions(all_moments, histogram, field_equations)
        assert input_polynomials(text, 96) == wanted
        actual, actual_metadata = backend.definitions(
            prime=2,
            ternary_prefix_sums=mode,
            histogram_e2=histogram,
            prefix_field_equations=field_equations,
        )
        assert text == actual and metadata == actual_metadata
        assert metadata["generators"] == len(wanted)
        assert metadata["transformed_original_cubic_domains"] == 100
        assert metadata["count_divisor"] == metadata["count_multiplier"] == 1
        assert metadata["prefix"] == "" and metadata["symmetry_normalization"] is False
        with patch.object(
            backend.subprocess, "run", side_effect=AssertionError("solver forbidden")
        ):
            result = backend.run(
                prepared / name,
                prime=2,
                ternary_prefix_sums=mode,
                histogram_e2=histogram,
                prefix_field_equations=field_equations,
                prepare_only=True,
                executable=HERE / "exact_msolve_f2_bitset_tools/msolve",
                require_export_marker=True,
            )
        assert (prepared / name).with_suffix(".ms").read_text() == text
        assert (
            result["status"] == "PREPARED_NOT_RUN" and result["basis_complete"] is False
        )
        assert "dimension_decimal" not in result and "board_count_decimal" not in result
        assert result["source_sha256"] == hashlib.sha256(text.encode()).hexdigest()
        variants.append(
            {
                "name": name,
                "generators": len(wanted),
                "input_sha256": result["source_sha256"],
                "status": result["status"],
                "count_divisor": 1,
                "input_file": str((prepared / name).with_suffix(".ms")),
            }
        )
    bad = [
        {"prime": 29},
        {"prefix": "0"},
        {"binary": True},
        {"fixture": "domain"},
        {"pivot_order": True},
        {"ternary_reduced": "all"},
    ]
    for changed in bad:
        options = {"prime": 2, "ternary_prefix_sums": "all"}
        options.update(changed)
        try:
            backend.definitions(**options)
        except ValueError:
            pass
        else:
            raise AssertionError("conflicting prefix-coordinate scope accepted")
    try:
        backend.definitions(prime=2, prefix_field_equations=True)
    except ValueError:
        pass
    else:
        raise AssertionError(
            "quartic field equations without transformed model accepted"
        )
    report = {
        "status": "PASS",
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "source_polynomials_compared": 100 + 72 + 8 + 96,
        "coordinate_inverse_basis_checks": 100,
        "original_domains_retained": 100,
        "optional_field_ideal_identities_checked": 100,
        "no_blanket_free_cubic_domains_added": True,
        "no_exponent_reduction_used": True,
        "moments_nonzero": 72,
        "vanished_moments": vanished,
        "elementary_ordinary_fourth_powers_preserved": True,
        "witness_checks": witness_checks,
        "complete_input_variants": variants,
        "invalid_scope_cases_rejected": 7,
        "solver_runs": 0,
        "full_count_status": "NOT_COMPUTED",
        "backend_sha256": hashlib.sha256(
            Path(backend.__file__).read_bytes()
        ).hexdigest(),
    }
    (HERE / "exact_pivot_review_prefix_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(
        json.dumps(
            {k: v for k, v in report.items() if k != "complete_input_variants"},
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
