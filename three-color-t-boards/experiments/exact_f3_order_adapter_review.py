#!/usr/bin/env python3
"""Audit actual backend wiring for the frozen F3 minimum-fill permutation."""

import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import exact_msolve_backend as backend
from exact_f3_review import parse_input
from exact_msolve_native_order import reorder

HERE = Path(__file__).resolve().parent


def main():
    options = {
        "prime": 3,
        "ternary_native_field": True,
        "native_translation": True,
        "native_e3": True,
    }
    base, base_metadata = backend.definitions(**options)
    source, metadata = backend.definitions(**options, native_order="minimum-fill")
    standalone, standalone_metadata = reorder(base, base_metadata)
    assert source == standalone and metadata == standalone_metadata
    assert source == (HERE / "exact_f3_order_selected.ms").read_text()
    mapping = json.loads((HERE / "exact_f3_order_selected.json").read_text())
    forward = mapping["old_index_to_new_index"]
    inverse = mapping["new_index_to_old_index"]
    before, after = parse_input(base), parse_input(source)
    assert len(before) == len(after) == 176
    for original, changed in zip(before, after, strict=False):
        assert changed == {
            tuple(sorted(forward[v] for v in term)): c for term, c in original.items()
        }
    assert after[95] == {(95, 95, 95): 1, (95,): 2}
    assert sum(any(95 in term for term in p) for p in after) == 1
    assert (
        metadata["old_index_to_new_index"] == forward
        and metadata["new_index_to_old_index"] == inverse
    )
    for name in ("original_color_linear_forms", "normalized_color_linear_forms"):
        wanted = {
            cell: {str(forward[int(v)]): c for v, c in form.items()}
            for cell, form in base_metadata[name].items()
        }
        assert metadata[name] == wanted
    assert (
        metadata["original_color_linear_forms"]
        == mapping["original_color_linear_forms_in_new_variables"]
    )
    assert metadata["free_normalized_prefix_variables"] == [
        base_metadata["free_normalized_prefix_variables"][old] for old in inverse[:95]
    ]
    assert (
        len(metadata["free_normalized_prefix_variables"])
        == len(set(metadata["free_normalized_prefix_variables"]))
        == 95
    )
    labels = metadata["equation_labels"]
    assert len(labels) == len(after)
    assert labels[96:] == base_metadata["equation_labels"][96:]
    assert sorted(int(label.split(":")[1]) for label in labels[:96]) == list(range(96))
    for label, polynomial in zip(labels[:96], after[:96], strict=False):
        i = int(label.split(":")[1])
        assert polynomial == {(i, i, i): 1, (i,): 2}
    for key, value in [
        ("variables", 96),
        ("coupled_variables", 95),
        ("generators", 176),
        ("prime", 3),
        ("field", "F3"),
        ("offset_variable_index", 95),
        ("count_divisor", 1),
        ("count_multiplier", 1),
        ("native_variable_order", "minimum-fill"),
        ("extension_variable", False),
        ("prefix", ""),
        ("fixed_original_cells", []),
        ("symmetry_normalization", False),
    ]:
        assert metadata[key] == value, (key, metadata[key])
    assert (
        metadata["translation_source_sha256"]
        == base_metadata["translation_source_sha256"]
    )
    assert (
        metadata["native_e3_source_sha256"] == base_metadata["native_e3_source_sha256"]
    )
    assert (
        metadata["pre_order_input_sha256"]
        == hashlib.sha256(base.encode()).hexdigest()
        == mapping["source_sha256"]
    )
    assert metadata["pre_e3_input_sha256"] == base_metadata["pre_e3_input_sha256"]
    assert (
        metadata["variable_order_source_sha256"]
        == hashlib.sha256(
            (HERE / "exact_f3_order_selected.json").read_bytes()
        ).hexdigest()
    )
    digest = hashlib.sha256(source.encode()).hexdigest()
    assert (
        metadata["input_sha256"]
        == digest
        == "b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd"
    )
    directory = HERE / "exact_f3_order_adapter_review_prepared"
    directory.mkdir(exist_ok=False)
    with patch.object(
        backend.subprocess, "run", side_effect=AssertionError("solver forbidden")
    ):
        prepared = backend.run(
            directory / "minimum_fill",
            **options,
            native_order="minimum-fill",
            prepare_only=True,
            require_export_marker=True,
            seconds=900,
            memory_mb=3072,
            max_pairs=16,
            executable=HERE / "exact_msolve_symbolic_reserve_tools/msolve",
            library_dir=HERE / "exact_algebra_backend_root/usr/lib",
        )
    saved = json.loads((directory / "minimum_fill.json").read_text())
    assert prepared == saved and (directory / "minimum_fill.ms").read_text() == source
    assert saved["status"] == "PREPARED_NOT_RUN" and saved["basis_complete"] is False
    assert saved["source_sha256"] == saved["input_sha256"] == digest
    assert (
        saved["variable_order_source_sha256"]
        == metadata["variable_order_source_sha256"]
    )
    assert saved["translation_source_sha256"] == metadata["translation_source_sha256"]
    assert saved["require_export_marker"] is True
    assert saved["timeout_seconds"] == 900 and saved["memory_mb"] == 3072
    assert "dimension_decimal" not in saved and "board_count_decimal" not in saved
    command = saved["command"]
    for flag, value in [
        ("-g", "1"),
        ("-l", "2"),
        ("-t", "1"),
        ("-r", "1"),
        ("-c", "0"),
        ("-m", "16"),
    ]:
        assert command[command.index(flag) + 1] == value
    executable_hash = hashlib.sha256(Path(command[0]).read_bytes()).hexdigest()
    assert (
        executable_hash
        == "a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a"
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
        {"native_translation": False},
        {"native_e3": False},
        {"native_order": "natural"},
        {"native_order": "minimum_fill"},
        {"native_order": False},
    ]
    for change in invalid:
        altered = dict(options, native_order="minimum-fill")
        altered.update(change)
        try:
            backend.definitions(**altered)
        except ValueError:
            pass
        else:
            raise AssertionError(("invalid ordering scope accepted", altered))
    bad_metadata = [
        ("prime", 2),
        ("variables", 95),
        ("native_translation", False),
        ("native_e3", False),
        ("offset_variable_index", 94),
        ("count_divisor", 3),
        ("count_multiplier", 3),
        ("prefix", "0"),
    ]
    for key, value in bad_metadata:
        changed = dict(base_metadata)
        changed[key] = value
        try:
            reorder(base, changed)
        except ValueError:
            pass
        else:
            raise AssertionError(("invalid reorder metadata accepted", key))
    try:
        reorder(base + "\n", base_metadata)
    except ValueError:
        pass
    else:
        raise AssertionError("modified input accepted despite frozen base hash")
    result = {
        "status": "PASS",
        "input_sha256": digest,
        "map_sha256": metadata["variable_order_source_sha256"],
        "pre_order_input_sha256": metadata["pre_order_input_sha256"],
        "variables": 96,
        "coupled_variables": 95,
        "generators": 176,
        "polynomials_compared": 176,
        "original_color_maps_compared": 100,
        "normalized_color_maps_compared": 100,
        "free_coordinate_positions_checked": 95,
        "field_equation_labels_checked": 96,
        "independent_offset_domain_present": True,
        "count_divisor": 1,
        "count_multiplier": 1,
        "extension_variable": False,
        "invalid_option_combinations": len(invalid),
        "invalid_metadata_cases": len(bad_metadata),
        "modified_input_rejected": True,
        "prepared_input": str(directory / "minimum_fill.ms"),
        "prepare_status": saved["status"],
        "executable_sha256": executable_hash,
        "adapter_sha256": saved["adapter_sha256"],
        "order_adapter_sha256": metadata["variable_order_adapter_sha256"],
        "solver_runs": 0,
        "full_count_status": "NOT_COMPUTED",
    }
    (HERE / "exact_f3_order_adapter_review_results.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
