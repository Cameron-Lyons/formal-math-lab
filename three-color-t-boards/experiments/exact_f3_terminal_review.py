#!/usr/bin/env python3
"""Audit the terminal full natural-F3 trial, never start or resume a solver."""

import hashlib
import json
import re
from datetime import UTC, datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
NAME = "exact_msolve_full_native3_e3_staged_3g"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main(name=NAME, translated=False, ordered=False):
    assert not ordered or translated
    byte_build = name == "exact_msolve_full_native3_minfill_byte_4g"
    assert not byte_build or (translated and ordered)
    if translated:
        if ordered:
            assert name in (
                "exact_msolve_full_native3_minfill_symbolic_3g",
                "exact_msolve_full_native3_minfill_symbolic_4g",
                "exact_msolve_full_native3_minfill_byte_4g",
            )
            input_hash = (
                "b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd"
            )
            report_name = (
                "exact_f3_order_terminal_review_results.json"
                if name.endswith("_3g")
                else "exact_f3_order_terminal_review_4g_results.json"
            )
            if byte_build:
                report_name = "exact_f3_byte_terminal_review_results.json"
        else:
            assert name == "exact_msolve_full_native3_translation_e3_symbolic_3g"
            input_hash = (
                "44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5"
            )
            report_name = "exact_f3_translation_terminal_review_results.json"
        pre_e3_hash = "339f10f7632c231f4e79a0b5c1e99700798fe7726c3b359ab097611ee650d3b1"
        executable_hash = (
            "a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a"
        )
        if byte_build:
            executable_hash = (
                "63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76"
            )
        map_key = "free_normalized_prefix_variables"
    else:
        assert name == NAME
        input_hash = "cb2497554585e51166b747cee0221efc3cf7f130f46b9084d7f2e9d3b760c105"
        pre_e3_hash = "e9e1163bd047fdca4000333d917a26e37dbf711abebca29d27fae6d49a2c34ba"
        executable_hash = (
            "9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a"
        )
        report_name = "exact_f3_terminal_review_results.json"
        map_key = "free_prefix_variables"
    stem = HERE / name
    result = json.loads(stem.with_suffix(".json").read_text())
    outer = json.loads(stem.with_suffix(".outer.json").read_text())
    assert (
        outer["status"] == "OUTER_PROCESS_FINISHED"
        and not outer["outer_wall_limit_reached"]
    )
    assert outer["backend_status"] == result["status"]
    log = stem.with_suffix(".log").read_text()
    assert result["status"] in stem.with_suffix(".outer.log").read_text()
    from exact_msolve_backend import definitions, parse_leading

    expected, metadata = definitions(
        prime=3,
        ternary_native_field=True,
        native_e3=True,
        native_translation=translated,
        native_order="minimum-fill" if ordered else None,
    )
    assert stem.with_suffix(".ms").read_text() == expected
    assert (
        sha(stem.with_suffix(".ms"))
        == result["source_sha256"]
        == metadata["input_sha256"]
    )
    assert result["source_sha256"] == input_hash
    assert result["pre_e3_input_sha256"] == pre_e3_hash
    assert result["executable_sha256"] == sha(Path(result["command"][0]))
    assert result["executable_sha256"] == executable_hash
    for key in (
        "variables",
        "generators",
        "field",
        "prime",
        "count_divisor",
        "count_multiplier",
        "native_field_source_sha256",
        "native_e3_source_sha256",
        map_key,
        "original_cell_order",
        "original_color_linear_forms",
        "prefix",
        "fixed_original_cells",
        "symmetry_normalization",
        "extension_variable",
    ):
        assert result[key] == metadata[key], key
    assert result["variables"] == 96 and result["generators"] == 176
    assert result["count_divisor"] == result["count_multiplier"] == 1
    preflight = None
    if translated:
        assert (
            result["native_translation"] is True and result["coupled_variables"] == 95
        )
        assert (
            result["offset_variable_index"] == 95
            and result["independent_offset_domain"] == "x96^3-x96"
        )
        assert (
            result["translation_source_sha256"] == metadata["translation_source_sha256"]
        )
        preflight = json.loads(stem.with_suffix(".preflight.json").read_text())
        if ordered:
            if byte_build:
                assert preflight["status"] == "LAUNCH"
                assert result["memory_mb"] == preflight["memory_cap_mb"] == 4096
                assert (
                    preflight["available_mb"]
                    >= preflight["required_available_mb"]
                    == 4608
                )
                assert result["timeout_seconds"] == preflight["seconds"] == 900
            else:
                selected = 4096 if preflight["mem_available_mib"] >= 4608 else 3072
                assert (
                    selected == result["memory_mb"] == preflight["selected_memory_mib"]
                )
                assert preflight["required_available_mib"] == selected + 512
                assert (
                    preflight["mem_available_mib"]
                    >= preflight["required_available_mib"]
                )
            assert (
                result["native_variable_order"]
                == metadata["native_variable_order"]
                == "minimum-fill"
            )
            for key in (
                "old_index_to_new_index",
                "new_index_to_old_index",
                "variable_order_source_sha256",
                "pre_order_input_sha256",
                "normalized_color_linear_forms",
                "equation_labels",
            ):
                assert result[key] == metadata[key], key
            assert (
                result["variable_order_source_sha256"]
                == "387d85417ffb7823ceef2984b506b39f6913169491d7ada2d75343ec1829bc3e"
            )
            if not byte_build:
                assert (
                    preflight["variable_order_source_sha256"]
                    == result["variable_order_source_sha256"]
                )
            assert (
                result["pre_order_input_sha256"]
                == "44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5"
            )
            if not byte_build:
                assert (
                    result["timeout_seconds"] == preflight["child_wall_seconds"] == 900
                )
                assert preflight["outer_wall_seconds"] == 960
        else:
            assert (
                preflight["mem_available_mib"]
                >= preflight["required_available_mib"]
                == 3584
            )
        assert preflight["executable_sha256"] == executable_hash
        if not byte_build:
            assert preflight["input_sha256"] == input_hash
            assert (
                preflight["model_source_sha256"] == result["translation_source_sha256"]
            )
            assert preflight["e3_source_sha256"] == result["native_e3_source_sha256"]
    assert "MSOLVE_F2_BITSET rows=" not in log
    markers = sum(
        line.strip() == "MSOLVE_PRIME_GB_EXPORT_COMPLETE" for line in log.splitlines()
    )
    assert result["export_marker_count"] == markers
    dimension = None
    board_count = None
    leading_exists = stem.with_suffix(".leading.json").exists()
    if result["status"] == "COMPLETE":
        assert result["returncode"] == 0 and outer["returncode"] == 0
        assert (
            markers == 1
            and result["basis_complete"] is True
            and not result["error_diagnostics"]
        )
        assert not re.search(
            r"\berror\b|failed|out of memory|cannot allocate|segmentation|aborted",
            log,
            re.IGNORECASE,
        )
        assert sha(stem.with_suffix(".basis")) == result["basis_sha256"]
        leading = parse_leading(stem.with_suffix(".basis").read_text(), 96, 3)
        exported = json.loads(stem.with_suffix(".leading.json").read_text())
        assert (
            exported["format"] == "leading-monomial-ideal-v1"
            and exported["variables"] == 96
        )
        assert (
            exported["standard_basis_complete"] is True
            and exported["leading_monomials"] == leading
        )
        assert exported["provenance"]["input_sha256"] == result["source_sha256"]
        assert (
            exported["provenance"]["executable_sha256"] == result["executable_sha256"]
        )
        assert exported["provenance"]["field"] == result["field"] == "F3"
        from exact_algebra_backend import monomial_dimension
        from exact_standard_monomials import count_standard_monomials

        first = count_standard_monomials(
            leading, 96, standard_basis_complete=True, max_states=1000000
        )
        second, _ = monomial_dimension(leading, 96, seconds=60)
        assert (
            first
            == second
            == int(result["dimension_decimal"])
            == int(result["board_count_decimal"])
        )
        assert first >= 45083592, (
            "full count conflicts with the established witness lower bound"
        )
        assert first % 12 == 0, (
            "full labeled count conflicts with free palette/reflection action"
        )
        dimension = board_count = str(first)
    else:
        assert result["status"] in (
            "BACKEND_ERROR",
            "INCOMPLETE_TIMEOUT",
            "POSTPROCESS_ERROR",
        )
        assert outer["returncode"] == 1
        assert "dimension_decimal" not in result and "board_count_decimal" not in result
        if result["status"] != "POSTPROCESS_ERROR":
            assert result["basis_complete"] is False and markers == 0
            assert stem.with_suffix(".basis").stat().st_size == 0 and not leading_exists
    headers = []
    current = None
    stages = []
    row_reserves = []
    symbolic_capacities = []
    promotions = []
    for line in log.splitlines():
        match = re.match(r"^\s*(\d+)\s+(\d+)\s+(\d+)(?:\s+(\d+)\s+x\s+(\d+))?", line)
        if match:
            current = {
                "degree": int(match[1]),
                "selected_pairs": int(match[2]),
                "pending_pairs_shown": int(match[3]),
                "matrix_rows": int(match[4]) if match[4] else None,
                "matrix_columns": int(match[5]) if match[5] else None,
                "round_timing_printed": False,
            }
            headers.append(current)
        # New allocation diagnostics may separate the selection header from
        # its later matrix dimensions. Associate that line with this round.
        dimensions = re.match(r"^\s*(\d+)\s+x\s+(\d+)\s+", line)
        if current is not None and dimensions:
            assert current["matrix_rows"] is None and current["matrix_columns"] is None
            current["matrix_rows"] = int(dimensions[1])
            current["matrix_columns"] = int(dimensions[2])
        if current is not None and re.match(r"^\s*\d+\.\d+\s*\|\s*\d+\.\d+\s*$", line):
            current["round_timing_printed"] = True
        if line.startswith("MSOLVE_SYMBOLIC_STAGING "):
            stages.append({k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", line)})
        if line.startswith("MSOLVE_SYMBOLIC_ROW_RESERVE "):
            row_reserves.append(
                {k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", line)}
            )
        if line.startswith("MSOLVE_SYMBOLIC_CAPACITY_REQUEST "):
            symbolic_capacities.append(
                {k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", line)}
            )
        if line.startswith("MSOLVE_PROMOTION_COLUMNS "):
            promotions.append({k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", line)})
    finished = [row for row in headers if row["round_timing_printed"] is True]
    diagnostics = [
        line
        for line in log.splitlines()
        if re.search(
            r"error|failed|out of memory|segmentation|aborted|cannot allocate",
            line,
            re.IGNORECASE,
        )
    ]
    record = {
        "name": name,
        "status": result["status"],
        "basis_complete": result["basis_complete"],
        "count_complete": dimension is not None,
        "quotient_dimension_decimal": dimension,
        "full_labeled_board_count_decimal": board_count,
        "count_scope": "full labeled boards",
        "variables": 96,
        "generators": 176,
        "prime": 3,
        "field": "F3",
        "count_divisor": 1,
        "count_multiplier": 1,
        "input_sha256": result["source_sha256"],
        "pre_e3_input_sha256": result["pre_e3_input_sha256"],
        "executable_sha256": result["executable_sha256"],
        "adapter_sha256": result.get("adapter_sha256"),
        "solver_cpu_seconds": result["child_cpu_seconds"],
        "solver_wall_seconds": result["child_wall_seconds"],
        "solver_wall_limit_seconds": result["timeout_seconds"],
        "memory_mb": result["memory_mb"],
        "solver_returncode": result.get("returncode"),
        "outer_returncode": outer["returncode"],
        "outer_wall_seconds": outer["elapsed_seconds"],
        "process_tree_cpu_seconds": outer["process_tree_cpu_seconds"],
        "outer_wall_limit_reached": False,
        "export_marker_count": markers,
        "basis_file_bytes": stem.with_suffix(".basis").stat().st_size,
        "leading_export_present": leading_exists,
        "completed_rounds_with_timing": len(finished),
        "last_completed_round": finished[-1] if finished else None,
        "last_started_round": headers[-1] if headers else None,
        "last_completed_promotion": promotions[-1] if promotions else None,
        "symbolic_staging_rounds": len(stages),
        "symbolic_staging_records": stages,
        "F2_bitset_rounds": 0,
        "raw_log_failure_diagnostics": diagnostics,
        "backend_error_diagnostics": result["error_diagnostics"],
        "solver_processes_started_by_this_audit": 0,
        "artifact_sha256": {
            suffix: sha(stem.with_suffix(suffix))
            for suffix in (
                ".json",
                ".outer.json",
                ".log",
                ".outer.log",
                ".ms",
                ".basis",
            )
        },
    }
    if translated:
        record.update(
            native_translation=True,
            coupled_variables=95,
            offset_variable_index=95,
            independent_offset_field_domain_retained=True,
            additional_factor_applied=1,
            translation_source_sha256=result["translation_source_sha256"],
            preflight=preflight,
            preflight_sha256=sha(stem.with_suffix(".preflight.json")),
            symbolic_row_reserve_count=len(row_reserves),
            last_symbolic_row_reserve=row_reserves[-1] if row_reserves else None,
            symbolic_capacity_request_count=len(symbolic_capacities),
            last_symbolic_capacity_request=symbolic_capacities[-1]
            if symbolic_capacities
            else None,
            maximum_requested_symbolic_exponent_capacity=max(
                (r["exponent_new"] for r in symbolic_capacities), default=None
            ),
        )
    if ordered:
        record.update(
            native_variable_order="minimum-fill",
            variable_order_source_sha256=result["variable_order_source_sha256"],
            pre_order_input_sha256=result["pre_order_input_sha256"],
            count_sanity_requirements={
                "established_lower_bound": 45083592,
                "divisible_by": 12,
            },
            count_sanity_checks_passed=dimension is not None,
        )
    if byte_build:
        record.update(
            exponent_storage_bytes=1,
            byte_build_review="exact_msolve_byte_review_notes.md",
            input_scope_verified_independently_of_preflight=True,
        )
        if result.get("returncode") == -11:
            record.update(
                termination_signal="SIGSEGV",
                underlying_failure_cause="Not established by the retained artifacts; a capacity request is not an allocation-failure diagnostic.",
            )
    output = {
        "status": "CHECKED_TERMINAL_ARTIFACTS",
        "audited_at_utc": datetime.now(UTC).isoformat(),
        "record": record,
        "semantics": "Only COMPLETE with successful marked basis export and matching independent integer counts supplies a count.",
    }
    (HERE / report_name).write_text(json.dumps(output, indent=2) + "\n")
    aggregate_path = HERE / "exact_msolve_current_trials_audit.json"
    aggregate = json.loads(aggregate_path.read_text())
    aggregate["trials"] = [r for r in aggregate["trials"] if r["name"] != name] + [
        record
    ]
    aggregate.update(
        last_audited_at_utc=output["audited_at_utc"],
        latest_audited_trials=[name],
        unrestricted_count=board_count,
        status="CHECKED_FULL_COUNT"
        if board_count is not None
        else "CHECKED_NO_FULL_COUNT",
        terminal_semantics=output["semantics"],
        solver_processes_started_by_this_audit=0,
    )
    aggregate_path.write_text(json.dumps(aggregate, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: v
                for k, v in record.items()
                if k not in ("artifact_sha256", "symbolic_staging_records")
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
