#!/usr/bin/env python3
"""Preparation and rejection checks only: never invoke msolve."""

import json
import tempfile
from dataclasses import replace
from pathlib import Path
from typing import Any

from exact_msolve_backend import definitions
from exact_msolve_cap_split import (
    ROOT,
    aggregate_msolve,
    audit_input,
    audit_msolve_result,
    model_name,
)
from exact_symmetry_split import AuditError, VerifiedCount, generate_manifest, read_json


def rejected(action):
    try:
        action()
    except AuditError, ValueError, KeyError:
        return
    raise AssertionError("bad artifact was accepted")


def main():
    manifest = generate_manifest(3)
    preparations = []
    with tempfile.TemporaryDirectory(prefix="exact_msolve_cap_audit_") as folder:
        folder = Path(folder)
        for case in manifest["cases"]:
            prefix = case["representative"]
            models = []
            for prime in (2, 29):
                source, metadata = definitions(
                    prime=prime, prefix=prefix, pivot_order=True
                )
                path = folder / f"{prefix}_{prime}.ms"
                path.write_text(source)
                audited = audit_input(path, prime, prefix, True)
                for key in (
                    "variables",
                    "generators",
                    "count_divisor",
                    "extension_variable",
                    "variable_original_cells",
                    "free_board_variables",
                ):
                    assert audited[key] == metadata[key], key
                models.append(audited)
            preparations.append(
                {
                    "prefix": prefix,
                    "orbit_weight": case["orbit_weight"],
                    "stabilizer_order": case["stabilizer_order"],
                    "raw_count_required_divisor": case["stabilizer_order"],
                    "models": models,
                }
            )
        # Recount retained artifacts, without rerunning the known solver fiber.
        known_path = ROOT / "experiments/exact_msolve_patched_fiber_six.json"
        known_data = read_json(known_path)
        record = audit_msolve_result(known_path, 29, known_data["prefix"])
        assert (
            record.count == 6
            and record.provenance["quotient_dimension_decimal"] == "12"
        )
        rejected(lambda: aggregate_msolve([record], 29))
        destination = folder / "mock.json"
        for suffix in (".ms", ".basis", ".log", ".leading.json"):
            destination.with_suffix(suffix).write_bytes(
                known_path.with_suffix(suffix).read_bytes()
            )
        base = dict(known_data)
        base["input_file"] = str(destination.with_suffix(".ms"))
        base["log_file"] = str(destination.with_suffix(".log"))
        base["command"] = list(base["command"])
        base["command"][16] = base["input_file"]
        base["command"][18] = str(destination.with_suffix(".basis"))
        destination.write_text(json.dumps(base))
        assert audit_msolve_result(destination, 29, record.prefix).count == 6
        bad_metadata: list[dict[str, Any]] = [
            {"status": s}
            for s in (
                "PREPARED_NOT_RUN",
                "INCOMPLETE_TIMEOUT",
                "BACKEND_ERROR",
                "POSTPROCESS_ERROR",
                "COMPLETE_FROM_LEADING_IDEAL",
            )
        ]
        bad_metadata += [
            {"prefix": "0000"},
            {"prime": 2},
            {"basis_complete": False},
            {"returncode": 1},
            {"returncode": False},
            {"require_export_marker": False},
            {"export_marker_count": 0},
            {"scope": "full labeled boards"},
            {"count_divisor": 1},
            {"board_count_decimal": "12"},
            {"dimension_decimal": "14", "board_count_decimal": "7"},
            {"dimension_decimal": "012"},
            {"orbit_canonical": True},
            {"count_multiplier": 12},
            {"threads": 2},
            {"linear_algebra": "probabilistic"},
            {"source_sha256": "0" * 64},
            {"basis_sha256": "0" * 64},
            {"executable_sha256": "0" * 64},
            {"variables": 19},
            {"moment_equations": 40},
            {"generators": 97},
            {"error_diagnostics": ["error"]},
            {"postprocess_error": "counter timeout"},
            {"dispersed_variable_order": True},
            {"variable_original_cells": []},
        ]
        for changed in bad_metadata:
            destination.write_text(json.dumps(dict(base, **changed)))
            rejected(lambda: audit_msolve_result(destination, 29, record.prefix))
        destination.write_text(json.dumps(base))
        log_path = destination.with_suffix(".log")
        original_log = log_path.read_text()
        marker = "MSOLVE_PRIME_GB_EXPORT_COMPLETE"
        for log in (
            original_log.replace(marker, ""),
            original_log + marker + "\n",
            original_log + "\nerror: failed\n",
        ):
            log_path.write_text(log)
            rejected(lambda: audit_msolve_result(destination, 29, record.prefix))
        log_path.write_text(original_log)
        # Metadata cannot disguise a different prefix, even with a correct hash.
        rejected(lambda: audit_input(destination.with_suffix(".ms"), 29, "0000"))
        rejected(lambda: audit_input(destination.with_suffix(".ms"), 2, record.prefix))
        synthetic = [
            VerifiedCount(
                c["representative"],
                model_name(2),
                3,
                10,
                c["stabilizer_order"],
                {"test_fixture": True},
            )
            for c in manifest["cases"]
        ]
        combined = aggregate_msolve(synthetic, 2)
        assert combined["full_count_decimal"] == "120"
        rejected(lambda: aggregate_msolve([], 2))
        rejected(lambda: aggregate_msolve(synthetic[:-1], 2))
        rejected(lambda: aggregate_msolve([*synthetic, synthetic[0]], 2))
        rejected(
            lambda: aggregate_msolve(
                [replace(synthetic[0], count=1), *synthetic[1:]], 2
            )
        )
        rejected(
            lambda: aggregate_msolve(
                [replace(synthetic[0], status="BACKEND_ERROR"), *synthetic[1:]], 2
            )
        )
        rejected(lambda: aggregate_msolve(synthetic, 29))
        zeros = [replace(item, count=0) for item in synthetic]
        assert aggregate_msolve(zeros, 2)["full_count_decimal"] == "0"
    actual = ROOT / "experiments/exact_msolve_cap0000_prime2.ms"
    actual_audit = audit_input(actual, 2, "0000", True)
    result_path = actual.with_suffix(".json")
    actual_status = (
        read_json(result_path)["status"]
        if result_path.exists()
        else "RUNNING_NO_RESULT"
    )
    if result_path.exists() and actual_status != "COMPLETE":
        rejected(lambda: audit_msolve_result(result_path, 2, "0000"))
    result = {
        "status": "PASS",
        "solver_processes_started": 0,
        "geometry_checked_cap_models": len(preparations) * 2,
        "rejected_metadata_cases": len(bad_metadata),
        "rejected_log_cases": 3,
        "aggregation_rejection_cases": 7,
        "synthetic_aggregation_is_not_a_board_count": True,
        "retained_known_fiber_audited_without_solver": {
            "raw_boards": 6,
            "quotient_dimension": 12,
        },
        "caps": preparations,
        "actual_cap0000_input": actual_audit,
        "actual_cap0000_terminal_status": actual_status,
        "full_ternary_count_status": "NOT_COMPUTED",
    }
    output = ROOT / "experiments/exact_msolve_cap_split_checks.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: v
                for k, v in result.items()
                if k not in ("caps", "actual_cap0000_input")
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
