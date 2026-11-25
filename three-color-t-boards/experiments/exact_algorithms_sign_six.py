#!/usr/bin/env python3
"""One bounded sign-model check with 81 actual original colors fixed.

The worker specializes the real backend definition using bilinear color
equations and runs the reviewed seventh executable once. The outer process
guards the solver plus both exact dimension counters. No full-board run.
"""

import argparse
import hashlib
import json
import os
import resource
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Any
from unittest.mock import patch

import exact_msolve_backend as backend
from exact_algorithms_sign_review import add, packed, parse
from exact_native_field_probe import SIX_PREFIX

HERE = Path(__file__).resolve().parent
STEM = HERE / "exact_algorithms_sign_six"
BINARY = HERE / "exact_msolve_symbolic_reserve_tools/msolve"
BINARY_SHA = "a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a"
MODEL = HERE / "exact_f3_sign_model.json"
MODEL_SHA = "a568c7b0341b54ba28d9c01cf000ac0c4fb8ecd89fb27abd9b678262d2ae85bc"
BASE_SHA = "dd0d371541d7a0ebbff559a854a08cd89219928e56e570265d29ef31b19fa381"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expression(polynomial):
    terms = []
    for monomial, coefficient in sorted(polynomial.items()):
        factors = [] if coefficient == 1 and monomial else [str(coefficient)]
        factors += [f"x{v + 1}" + (f"^{e}" if e != 1 else "") for v, e in monomial]
        terms.append("*".join(factors))
    return "+".join(terms) or "0"


def limits():
    limit = 2 * 1024**3
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def worker():
    if any(
        STEM.with_suffix(s).exists()
        for s in (".ms", ".basis", ".log", ".json", ".leading.json", ".fixes.json")
    ):
        raise ValueError("refusing to overwrite prior fixture artifacts")
    assert digest(BINARY) == BINARY_SHA and digest(MODEL) == MODEL_SHA
    model = json.loads(MODEL.read_text())
    original_definitions = backend.definitions
    source, metadata = original_definitions(
        prime=3,
        ternary_native_field=True,
        native_e3=True,
        native_translation=True,
        native_sign=True,
    )
    assert hashlib.sha256(source.encode()).hexdigest() == BASE_SHA
    assert len(SIX_PREFIX) == 81 and SIX_PREFIX[0] == "1"
    assert parse(source)[0] == 97 and len(parse(source)[1]) == 179
    fixes: list[dict[str, Any]] = []
    for cell, digit in enumerate(SIX_PREFIX):
        form = packed(model["original_color_bilinear_polynomials"][str(cell)])
        p = add(form, {(): -int(digit)})
        fixes.append(
            {
                "original_cell": cell,
                "color": int(digit),
                "bilinear_form": model["original_color_bilinear_polynomials"][
                    str(cell)
                ],
                "polynomial": expression(p),
            }
        )
        assert parse(
            "x"
            + ",x".join(str(i + 1) for i in range(97))
            + "\n3\n"
            + fixes[-1]["polynomial"]
            + "\n"
        )[1] == [p]
    assert fixes[0]["polynomial"] == "2+x96"
    specialized = (
        source.rstrip("\n") + ",\n" + ",\n".join(f["polynomial"] for f in fixes) + "\n"
    )
    n, polynomials = parse(specialized)
    assert n == 97 and len(polynomials) == 260
    metadata.update(
        model="ternary-native-field-f3-affine-factors-fixed-original-prefix",
        scope="completions of a fixed 81-original-cell prefix; not unrestricted",
        count_scope="fixed original-color prefix",
        prefix=SIX_PREFIX,
        fixed_original_cells=list(range(81)),
        fixed_cell_count=81,
        fixed_prefix_rows=9,
        generators=260,
        base_generator_count=179,
        base_input_sha256=BASE_SHA,
        original_color_fix_rule="z_cell=a+s*d_cell; exact bilinear forms minus requested color",
        fixed_original_apex=1,
        expected_offset=1,
        expected_sign=1,
        expected_dimension_decimal="6",
        count_divisor=1,
        count_multiplier=1,
        outer_timeout_seconds=60,
        validation_fixture=True,
        full_count_status="UNEVALUATED",
    )
    STEM.with_suffix(".fixes.json").write_text(json.dumps(fixes, indent=2) + "\n")
    # The wrapper is local to this worker and leaves the shared backend unchanged.
    with patch.object(
        backend, "definitions", lambda *args, **kwargs: (specialized, metadata.copy())
    ):
        result = backend.run(
            STEM,
            prime=3,
            ternary_native_field=True,
            native_e3=True,
            native_translation=True,
            native_sign=True,
            seconds=30,
            memory_mb=2048,
            executable=BINARY,
            max_pairs=16,
            require_export_marker=True,
        )
    result.update(
        log_sha256=digest(STEM.with_suffix(".log")),
        fixes_sha256=digest(STEM.with_suffix(".fixes.json")),
        specialization_worker_sha256=digest(Path(__file__)),
    )
    if result.get("status") == "COMPLETE":
        assert result["dimension_decimal"] == result["board_count_decimal"] == "6", (
            result
        )
        result["known_six_prefix_verified"] = True
    STEM.with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {
                k: result.get(k)
                for k in (
                    "status",
                    "dimension_decimal",
                    "board_count_decimal",
                    "child_wall_seconds",
                    "child_cpu_seconds",
                    "basis_size",
                    "basis_complete",
                    "export_marker_count",
                    "error_diagnostics",
                    "source_sha256",
                )
            }
        ),
        flush=True,
    )
    return 0 if result.get("known_six_prefix_verified") else 1


def outer():
    outer_path = STEM.with_suffix(".outer.json")
    log_path = STEM.with_suffix(".outer.log")
    if outer_path.exists() or log_path.exists():
        raise ValueError("prior outer artifacts exist")
    command = [sys.executable, str(Path(__file__).resolve()), "--child"]
    started = time.monotonic()
    record: dict[str, Any] = {
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
            record["returncode"] = code
            record["status"] = "COMPLETE" if code == 0 else "CHILD_ERROR"
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            record["status"] = "OUTER_TIMEOUT"
    record["elapsed_seconds"] = time.monotonic() - started
    outer_path.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))
    print(log_path.read_text())
    return 0 if record["status"] == "COMPLETE" else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--child", action="store_true")
    args = parser.parse_args()
    raise SystemExit(worker() if args.child else outer())
