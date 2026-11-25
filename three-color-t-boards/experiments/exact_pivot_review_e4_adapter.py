#!/usr/bin/env python3
"""Audit four actual e4 backend/preparation modes, with solver calls forbidden."""

import hashlib
import json
from itertools import product
from pathlib import Path
from unittest.mock import patch

import exact_msolve_backend as backend
from exact_pivot_review_common import decode_polynomials, input_polynomials

HERE = Path(__file__).resolve().parent


def main():
    source = HERE / "exact_pivot_math_prefix_e4_constraints.json"
    assert (
        hashlib.sha256(source.read_bytes()).hexdigest()
        == "dadaa5f4caf17b00311abe9000cf5463e101946bfc0ab9b2fb319f26838e8a91"
    )
    model = json.loads(source.read_text())
    expected = list(decode_polynomials(model["equations"], 96, 4, 4).values())
    assert list(map(len, expected)) == [12324, 1146, 278, 446]
    folder = HERE / "exact_pivot_review_e4_prepared"
    folder.mkdir(exist_ok=False)
    reports = []
    for all_moments, fields in product((False, True), repeat=2):
        mode = "all" if all_moments else "representatives"
        name = f"{mode}_field{int(fields)}"
        options = {
            "prime": 2,
            "ternary_prefix_sums": mode,
            "histogram_e2": True,
            "prefix_field_equations": fields,
        }
        base, base_metadata = backend.definitions(**options)
        previous = (
            HERE / "exact_pivot_review_prefix_prepared" / f"{mode}_e1_f{int(fields)}.ms"
        )
        assert base == previous.read_text()
        text, metadata = backend.definitions(**options, histogram_e4=True)
        assert text.startswith(base.rstrip("\n") + ",\n")
        assert input_polynomials(text, 96)[-4:] == expected
        assert all(
            len(term) == 4 for p in input_polynomials(text, 96)[-4:] for term in p
        )
        assert metadata["free_prefix_variables"] == model["free_prefix_variables"]
        assert metadata["original_cell_order"] == model["original_cell_order"]
        assert (
            metadata["transformed_original_cubic_domains"] == 100
            and metadata["variables"] == 96
        )
        assert metadata["generators"] == base_metadata["generators"] + 4
        assert metadata["count_divisor"] == metadata["count_multiplier"] == 1
        assert metadata["prefix"] == "" and metadata["symmetry_normalization"] is False
        assert metadata["histogram_e2"] is True and metadata["histogram_e4"] is True
        assert metadata["elementary_e4_generators"] == 4
        assert (
            metadata["pre_e4_input_sha256"] == hashlib.sha256(base.encode()).hexdigest()
        )
        assert metadata["input_sha256"] == hashlib.sha256(text.encode()).hexdigest()
        assert metadata["equation_labels"] == base_metadata["equation_labels"] + [
            eq["label"] for eq in model["equations"]
        ]
        with patch.object(
            backend.subprocess, "run", side_effect=AssertionError("no solver permitted")
        ):
            result = backend.run(
                folder / name,
                **options,
                histogram_e4=True,
                prepare_only=True,
                executable=HERE / "exact_msolve_f2_bitset_tools/msolve",
                require_export_marker=True,
            )
        assert (folder / name).with_suffix(".ms").read_text() == text
        assert (
            result["status"] == "PREPARED_NOT_RUN" and result["basis_complete"] is False
        )
        assert "board_count_decimal" not in result and "dimension_decimal" not in result
        assert result["source_sha256"] == hashlib.sha256(text.encode()).hexdigest()
        reports.append(
            {
                "mode": name,
                "variables": 96,
                "generators": result["generators"],
                "base_generators": base_metadata["generators"],
                "count_divisor": 1,
                "base_retained_verbatim": True,
                "ordinary_quartic_terms": list(map(len, expected)),
                "input_sha256": result["source_sha256"],
                "pre_e4_input_sha256": metadata["pre_e4_input_sha256"],
                "status": result["status"],
                "input_file": str((folder / name).with_suffix(".ms")),
            }
        )
    baseline = {
        "prime": 2,
        "ternary_prefix_sums": "all",
        "histogram_e2": True,
        "histogram_e4": True,
    }
    invalid = [
        {"ternary_prefix_sums": None},
        {"histogram_e2": False},
        {"prime": 29},
        {"prefix": "0"},
        {"binary": True},
        {"fixture": "domain"},
        {"pivot_order": True},
        {"ternary_reduced": "all"},
        {"ternary_prefix_sums": "invalid"},
    ]
    for change in invalid:
        try:
            backend.definitions(**dict(baseline, **change))
        except ValueError:
            pass
        else:
            raise AssertionError("invalid e4 scope accepted")
    report = {
        "status": "PASS",
        "solver_calls": 0,
        "variants": reports,
        "invalid_scope_cases_rejected": len(invalid),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "adapter_sha256": hashlib.sha256(
            (HERE / "exact_msolve_prefix_e4.py").read_bytes()
        ).hexdigest(),
        "backend_sha256": hashlib.sha256(
            Path(backend.__file__).read_bytes()
        ).hexdigest(),
        "full_count_status": "NOT_COMPUTED",
    }
    (HERE / "exact_pivot_review_e4_adapter_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
