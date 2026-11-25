#!/usr/bin/env python3
"""Bounded fixed-prefix verification of four affine-eliminated branches."""

import argparse
import hashlib
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Any
from unittest.mock import patch

import exact_msolve_backend as backend
from exact_algorithms_branch_elimination_review import MANIFEST_SHA, parse
from exact_algorithms_sign_review import add, packed
from exact_algorithms_sign_six import BINARY, BINARY_SHA, digest, expression, limits
from exact_native_field_probe import SIX_PREFIX

HERE = Path(__file__).resolve().parent


def worker(branch):
    stem = HERE / f"exact_algorithms_eliminated_six_{branch}"
    n = 96 - branch
    if any(
        stem.with_suffix(s).exists()
        for s in [".ms", ".basis", ".json", ".log", ".leading.json", ".fixes.json"]
    ):
        raise ValueError("refusing to overwrite fixture")
    assert digest(BINARY) == BINARY_SHA
    manifest_path = HERE / "exact_f3_branch_elimination_manifest.json"
    assert digest(manifest_path) == MANIFEST_SHA
    manifest = json.loads(manifest_path.read_text())
    rep = manifest["branches"][branch]["representations"][0]
    source, metadata = backend.definitions(
        prime=3,
        ternary_native_field=True,
        native_e3=True,
        native_translation=True,
        native_sign_branch=branch,
        native_branch_elimination=True,
    )
    base_hash = hashlib.sha256(source.encode()).hexdigest()
    assert base_hash == rep["input_sha256"]
    assert parse(source)[0] == n and len(parse(source)[1]) == n + 81
    fixes: list[dict[str, Any]] = []
    for cell, digit in enumerate(SIX_PREFIX):
        form = metadata["original_color_polynomials"][str(cell)]
        p = add(packed(form), {(): -int(digit)})
        fixes.append(
            {
                "original_cell": cell,
                "color": int(digit),
                "original_color_polynomial": form,
                "polynomial": expression(p),
            }
        )
    assert fixes[0]["polynomial"] == f"2+x{n - 1}"
    specialized = (
        source.rstrip("\n") + ",\n" + ",\n".join(f["polynomial"] for f in fixes) + "\n"
    )
    actual_n, polys = parse(specialized)
    assert actual_n == n and len(polys) == n + 162
    for cell, digit in enumerate(SIX_PREFIX):
        assert polys[n + 81 + cell] == add(
            packed(fixes[cell]["original_color_polynomial"]), {(): -int(digit)}
        )
    expected = "6" if branch == 0 else "0"
    metadata["base_full_count_rule"] = metadata.pop("full_count_rule")
    metadata.update(
        model="ternary-native-field-f3-affine-eliminated-branch-fixed-original-prefix",
        scope=f"completions of a fixed81-original-cell prefix in affine-eliminated branch{branch}; not unrestricted",
        count_scope=f"fixed original-color prefix in branch {branch}",
        prefix=SIX_PREFIX,
        fixed_original_cells=list(range(81)),
        fixed_cell_count=81,
        fixed_prefix_rows=9,
        generators=n + 162,
        base_generator_count=n + 81,
        base_input_sha256=base_hash,
        original_color_fix_rule="a+s*d_cell-color, including every affine constant term in d_cell",
        expected_dimension_decimal=expected,
        expected_offset=1,
        prefix_selected_difference=[1, 2, 0, 2],
        prefix_first_nonzero_branch=0,
        count_divisor=1,
        count_multiplier=1,
        outer_timeout_seconds=60,
        validation_fixture=True,
        full_count_status="UNEVALUATED",
        fixed_prefix_count_rule="sum exactly one completed count per branch",
    )
    if branch == 0:
        metadata["expected_sign"] = 1
    stem.with_suffix(".fixes.json").write_text(json.dumps(fixes, indent=2) + "\n")
    with patch.object(
        backend, "definitions", lambda *args, **kwargs: (specialized, metadata.copy())
    ):
        result = backend.run(
            stem,
            prime=3,
            ternary_native_field=True,
            native_e3=True,
            native_translation=True,
            native_sign_branch=branch,
            native_branch_elimination=True,
            seconds=30,
            memory_mb=2048,
            executable=BINARY,
            max_pairs=16,
            require_export_marker=True,
        )
    result.update(
        log_sha256=digest(stem.with_suffix(".log")),
        fixes_sha256=digest(stem.with_suffix(".fixes.json")),
        specialization_worker_sha256=digest(Path(__file__)),
    )
    if result.get("status") == "COMPLETE":
        if (
            result["dimension_decimal"] == result["board_count_decimal"] == expected
            and result.get("basis_complete") is True
            and result.get("standard_basis_complete") is True
        ):
            result["known_prefix_branch_dimension_verified"] = True
        else:
            result.update(
                status="VALIDATION_ERROR",
                validation_error="unexpected count or completion flags",
            )
    stem.with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: result.get(k)
                for k in [
                    "status",
                    "native_sign_branch",
                    "variables",
                    "generators",
                    "dimension_decimal",
                    "child_cpu_seconds",
                    "child_wall_seconds",
                    "basis_size",
                    "export_marker_count",
                    "error_diagnostics",
                    "basis_complete",
                    "standard_basis_complete",
                ]
            }
        ),
        flush=True,
    )
    return 0 if result.get("known_prefix_branch_dimension_verified") else 1


def outer():
    report = HERE / "exact_algorithms_eliminated_six_results.json"
    if report.exists():
        raise ValueError("prior aggregate result exists")
    results: list[dict[str, Any]] = []
    for branch in range(4):
        stem = HERE / f"exact_algorithms_eliminated_six_{branch}"
        path = stem.with_suffix(".outer.json")
        log_path = stem.with_suffix(".outer.log")
        if path.exists() or log_path.exists():
            raise ValueError("prior outer artifacts exist")
        command = [
            sys.executable,
            str(Path(__file__).resolve()),
            "--child",
            str(branch),
        ]
        started = time.monotonic()
        record: dict[str, Any] = {
            "branch": branch,
            "command": command,
            "status": "RUNNING",
            "timeout_seconds": 60,
            "memory_limit_bytes": 2 * 1024**3,
        }
        path.write_text(json.dumps(record, indent=2) + "\n")
        with log_path.open("x") as log:
            p = subprocess.Popen(
                command,
                stdout=log,
                stderr=subprocess.STDOUT,
                preexec_fn=limits,  # noqa: PLW1509
                start_new_session=True,
            )
            try:
                code = p.wait(timeout=60)
                record.update(
                    returncode=code, status="COMPLETE" if code == 0 else "CHILD_ERROR"
                )
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                record["status"] = "OUTER_TIMEOUT"
        record["elapsed_seconds"] = time.monotonic() - started
        if stem.with_suffix(".json").exists():
            r = json.loads(stem.with_suffix(".json").read_text())
            record.update(
                {
                    k: r.get(k)
                    for k in [
                        "dimension_decimal",
                        "basis_complete",
                        "standard_basis_complete",
                        "child_cpu_seconds",
                        "child_wall_seconds",
                        "known_prefix_branch_dimension_verified",
                    ]
                }
            )
        path.write_text(json.dumps(record, indent=2) + "\n")
        results.append(record)
        print(json.dumps(record), flush=True)
        print(log_path.read_text(), flush=True)
    complete = all(
        r["status"] == "COMPLETE" and r.get("known_prefix_branch_dimension_verified")
        for r in results
    )
    summary = {
        "status": "COMPLETE" if complete else "INCOMPLETE",
        "scope": "four affine-eliminated branches of a fixed known-six prefix; not unrestricted",
        "cases": results,
        "expected_dimensions": ["6", "0", "0", "0"],
        "full_solver_runs": 0,
        "all_worker_processes_terminal": True,
    }
    if complete:
        summary["exact_branch_dimensions"] = [r["dimension_decimal"] for r in results]
        summary["fixed_prefix_total_decimal"] = str(
            sum(int(r["dimension_decimal"]) for r in results)
        )
    report.write_text(json.dumps(summary, indent=2) + "\n")
    return 0 if complete else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--child", type=int, choices=range(4))
    args = parser.parse_args()
    raise SystemExit(worker(args.child) if args.child is not None else outer())
