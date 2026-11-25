#!/usr/bin/env python3
"""Four sequential bounded known-six prefix checks of disjoint branch ideals."""

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
from exact_algorithms_sign_review import add, packed, parse
from exact_algorithms_sign_six import BINARY, BINARY_SHA, digest, expression, limits
from exact_native_field_probe import SIX_PREFIX

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "exact_f3_sign_branches_manifest.json"
MANIFEST_SHA = "9ecb49f828699a3966c0349bddb4bc4f57cc163b65ba1855770357bf2e39d2c7"


def worker(branch):
    stem = HERE / f"exact_algorithms_branch_six_{branch}"
    if any(
        stem.with_suffix(s).exists()
        for s in (".ms", ".basis", ".log", ".json", ".leading.json", ".fixes.json")
    ):
        raise ValueError("refusing to overwrite branch fixture artifacts")
    assert digest(BINARY) == BINARY_SHA and digest(MANIFEST) == MANIFEST_SHA
    manifest = json.loads(MANIFEST.read_text())
    source, metadata = backend.definitions(
        prime=3,
        ternary_native_field=True,
        native_e3=True,
        native_translation=True,
        native_sign_branch=branch,
    )
    base_hash = hashlib.sha256(source.encode()).hexdigest()
    assert base_hash == manifest["branches"][branch]["natural_sha256"]
    assert parse(source)[0] == 97 and len(parse(source)[1]) == 179 + branch
    fixes: list[dict[str, Any]] = []
    for cell, digit in enumerate(SIX_PREFIX):
        form = metadata["original_color_bilinear_polynomials"][str(cell)]
        p = add(packed(form), {(): -int(digit)})
        fixes.append(
            {
                "original_cell": cell,
                "color": int(digit),
                "bilinear_form": form,
                "polynomial": expression(p),
            }
        )
    assert fixes[0]["polynomial"] == "2+x96"
    specialized = (
        source.rstrip("\n") + ",\n" + ",\n".join(f["polynomial"] for f in fixes) + "\n"
    )
    n, polys = parse(specialized)
    assert n == 97 and len(polys) == 260 + branch
    for cell, digit in enumerate(SIX_PREFIX):
        assert polys[179 + branch + cell] == add(
            packed(fixes[cell]["bilinear_form"]), {(): -int(digit)}
        )
    expected = "6" if branch == 0 else "0"
    metadata["base_full_count_rule"] = metadata.pop("full_count_rule")
    metadata.update(
        model="ternary-native-field-f3-affine-linear-branch-fixed-original-prefix",
        scope=f"completions of a fixed 81-original-cell prefix in branch {branch}; not unrestricted",
        count_scope=f"fixed original-color prefix in branch {branch}",
        prefix=SIX_PREFIX,
        fixed_original_cells=list(range(81)),
        fixed_cell_count=81,
        fixed_prefix_rows=9,
        generators=260 + branch,
        base_generator_count=179 + branch,
        base_input_sha256=base_hash,
        original_color_fix_rule="z_cell=a+s*d_cell; exact bilinear forms minus requested color",
        fixed_original_apex=1,
        expected_dimension_decimal=expected,
        prefix_selected_difference=[1, 2, 0, 2],
        prefix_first_nonzero_branch=0,
        count_divisor=1,
        count_multiplier=1,
        outer_timeout_seconds=60,
        validation_fixture=True,
        full_count_status="UNEVALUATED",
        fixed_prefix_count_rule="sum exactly one completed count for each branch 0,1,2,3",
    )
    if branch == 0:
        metadata.update(expected_offset=1, expected_sign=1)
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
            result["dimension_decimal"] != expected
            or result["board_count_decimal"] != expected
        ):
            result.update(
                status="VALIDATION_ERROR", validation_error="unexpected exact dimension"
            )
        else:
            result["known_prefix_branch_dimension_verified"] = True
    stem.with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: result.get(k)
                for k in [
                    "status",
                    "native_sign_branch",
                    "dimension_decimal",
                    "child_cpu_seconds",
                    "child_wall_seconds",
                    "basis_size",
                    "export_marker_count",
                    "error_diagnostics",
                ]
            }
        ),
        flush=True,
    )
    return 0 if result.get("known_prefix_branch_dimension_verified") else 1


def outer():
    report = HERE / "exact_algorithms_branch_six_results.json"
    if report.exists():
        raise ValueError("refusing to overwrite aggregate result")
    results: list[dict[str, Any]] = []
    for branch in range(4):
        stem = HERE / f"exact_algorithms_branch_six_{branch}"
        outer_path = stem.with_suffix(".outer.json")
        log_path = stem.with_suffix(".outer.log")
        if outer_path.exists() or log_path.exists():
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
            "timeout_seconds": 60,
            "memory_limit_bytes": 2 * 1024**3,
            "status": "RUNNING",
        }
        outer_path.write_text(json.dumps(record, indent=2) + "\n")
        with log_path.open("x") as log:
            process = subprocess.Popen(
                command,
                stdout=log,
                stderr=subprocess.STDOUT,
                preexec_fn=limits,  # noqa: PLW1509
                start_new_session=True,
            )
            try:
                code = process.wait(timeout=60)
                record.update(
                    returncode=code, status="COMPLETE" if code == 0 else "CHILD_ERROR"
                )
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                record["status"] = "OUTER_TIMEOUT"
        record["elapsed_seconds"] = time.monotonic() - started
        outer_path.write_text(json.dumps(record, indent=2) + "\n")
        if stem.with_suffix(".json").exists():
            result = json.loads(stem.with_suffix(".json").read_text())
            record.update(
                {
                    k: result.get(k)
                    for k in [
                        "dimension_decimal",
                        "basis_complete",
                        "child_cpu_seconds",
                        "child_wall_seconds",
                        "known_prefix_branch_dimension_verified",
                    ]
                }
            )
        results.append(record)
        print(json.dumps(record), flush=True)
        print(log_path.read_text(), flush=True)
    complete = all(
        r["status"] == "COMPLETE" and r.get("known_prefix_branch_dimension_verified")
        for r in results
    )
    summary = {
        "status": "COMPLETE" if complete else "INCOMPLETE",
        "scope": "four disjoint branches of the fixed known-six prefix; not unrestricted",
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
