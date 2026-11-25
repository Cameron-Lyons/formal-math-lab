#!/usr/bin/env python3
"""Audit both actual translation backend modes, without solver execution."""

import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import exact_msolve_backend as backend
from exact_f3_review import decode, parse_input
from exact_msolve_translation import translation_definitions

HERE = Path(__file__).resolve().parent


def main():
    data = json.loads((HERE / "exact_f3_translation_model.json").read_text())
    extra = json.loads((HERE / "exact_f3_translation_e3_constraints.json").read_text())
    directory = HERE / "exact_f3_translation_review_prepared"
    directory.mkdir(exist_ok=False)
    reports = []
    for e3 in (False, True):
        name = "with_e3" if e3 else "base"
        source, metadata = backend.definitions(
            prime=3, ternary_native_field=True, native_translation=True, native_e3=e3
        )
        direct, direct_metadata = translation_definitions(e3)
        assert source == direct and metadata == direct_metadata
        expected = list(decode(data["domain_equations"]).values()) + list(
            decode(data["moment_equations"]).values()
        )
        if e3:
            expected += list(decode(extra["equations"]).values())
        actual = parse_input(source)
        assert actual == expected
        assert actual[95] == {(95, 95, 95): 1, (95,): 2}
        assert sum(any(95 in term for term in p) for p in actual) == 1
        assert metadata["variables"] == 96 and metadata["generators"] == len(
            expected
        ) == (176 if e3 else 172)
        assert (
            metadata["coupled_variables"] == 95
            and metadata["offset_variable_index"] == 95
        )
        assert metadata["count_divisor"] == metadata["count_multiplier"] == 1
        assert metadata["field"] == "F3" and metadata["extension_variable"] is False
        assert (
            metadata["prefix"] == ""
            and metadata["fixed_original_cells"] == []
            and metadata["symmetry_normalization"] is False
        )
        assert (
            metadata["original_color_linear_forms"]
            == data["original_color_linear_forms"]
        )
        assert (
            metadata["free_normalized_prefix_variables"]
            == data["free_normalized_prefix_variables"]
        )
        assert (
            metadata["native_field_source_sha256"]
            == metadata["translation_source_sha256"]
            == hashlib.sha256(
                (HERE / "exact_f3_translation_model.json").read_bytes()
            ).hexdigest()
        )
        frozen = HERE / (
            "exact_f3_translation_e3.ms" if e3 else "exact_f3_translation_model.ms"
        )
        assert source == frozen.read_text()
        digest = hashlib.sha256(source.encode()).hexdigest()
        with patch.object(
            backend.subprocess, "run", side_effect=AssertionError("solver forbidden")
        ):
            prepared = backend.run(
                directory / name,
                prime=3,
                ternary_native_field=True,
                native_translation=True,
                native_e3=e3,
                prepare_only=True,
                require_export_marker=True,
                executable=HERE / "exact_msolve_staged_f3_tools/msolve",
            )
        assert (directory / name).with_suffix(".ms").read_text() == source
        assert (
            prepared["status"] == "PREPARED_NOT_RUN"
            and prepared["basis_complete"] is False
        )
        assert prepared["source_sha256"] == prepared["input_sha256"] == digest
        assert (
            prepared["translation_source_sha256"]
            == metadata["translation_source_sha256"]
        )
        assert (
            prepared["untranslated_source_sha256"] == data["source_native_model_sha256"]
        )
        assert (
            "dimension_decimal" not in prepared
            and "board_count_decimal" not in prepared
        )
        reports.append(
            {
                "mode": name,
                "generators": len(expected),
                "input_sha256": digest,
                "prepared_path": str((directory / name).with_suffix(".ms")),
                "count_divisor": 1,
                "count_multiplier": 1,
                "status": prepared["status"],
                "independent_apex_domain_present": True,
            }
        )
    assert (
        (directory / "with_e3.ms")
        .read_text()
        .startswith((directory / "base.ms").read_text().rstrip("\n") + ",\n")
    )
    invalid = [
        {"prime": 2},
        {"prime": 29},
        {"prefix": "0"},
        {"binary": True},
        {"fixture": "domain"},
        {"pivot_order": True},
        {"ternary_reduced": "all"},
        {"ternary_prefix_sums": "all"},
        {"histogram_e2": True},
        {"histogram_e4": True},
        {"prefix_field_equations": True},
        {"ternary_native_field": False},
    ]
    for e3 in (False, True):
        for change in invalid:
            options = {
                "prime": 3,
                "ternary_native_field": True,
                "native_translation": True,
                "native_e3": e3,
            }
            options.update(change)
            try:
                backend.definitions(**options)
            except ValueError:
                pass
            else:
                raise AssertionError(
                    ("conflicting translation scope accepted", options)
                )
    for value in (None, 0, 1, "all"):
        try:
            translation_definitions(value)
        except ValueError:
            pass
        else:
            raise AssertionError(("non-Boolean augmentation accepted", value))
    result = {
        "status": "PASS",
        "variants": reports,
        "actual_polynomials_compared": 348,
        "invalid_option_combinations": 24,
        "invalid_non_boolean_options": 4,
        "complete_original_count_factor_preserved_inside_input": True,
        "offset_is_not_extension": True,
        "adapter_sha256": hashlib.sha256(
            Path(backend.__file__).read_bytes()
        ).hexdigest(),
        "translation_exporter_sha256": hashlib.sha256(
            (HERE / "exact_msolve_translation.py").read_bytes()
        ).hexdigest(),
        "solver_runs": 0,
        "full_count_status": "NOT_COMPUTED",
    }
    (HERE / "exact_f3_translation_adapter_review_results.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
