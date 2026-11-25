#!/usr/bin/env python3
"""One bounded validation of the translated F3 model with81 original colors fixed.

Default mode supplies a60-second outer guard. The internal worker launches
exactly one reviewed6b msolve child, with30seconds and2GiB. Existing artifacts
are never overwritten. This fixture is not an unrestricted count.
"""

import argparse
import hashlib
import json
import os
import re
import resource
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

from exact_algebra_backend import monomial_dimension
from exact_f3_math import expression, field_rank
from exact_msolve_backend import parse_leading
from exact_native_field_probe import SIX_PREFIX
from exact_standard_monomials import count_standard_monomials

HERE = Path(__file__).resolve().parent
STEM = HERE / "exact_f3_translation_six"
BINARY = HERE / "exact_msolve_staged_f3_tools/msolve"
BINARY_SHA = "9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a"
MODEL = HERE / "exact_f3_translation_model.json"
MODEL_SHA = "1e2dc884f8996c6bd1b5093f24fa6fe7d7f1002e97b69762baadfda5adf94a7f"
BASE = HERE / "exact_f3_translation_e3.ms"
BASE_SHA = "44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save_result(record):
    STEM.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")


def limits():
    limit = 2 * 1024**3
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def worker():
    for suffix in (".ms", ".basis", ".log", ".json", ".leading.json", ".fixes.json"):
        if STEM.with_suffix(suffix).exists():
            raise ValueError("refusing to overwrite " + str(STEM.with_suffix(suffix)))
    assert (
        digest(BINARY) == BINARY_SHA
        and digest(MODEL) == MODEL_SHA
        and digest(BASE) == BASE_SHA
    )
    model = json.loads(MODEL.read_text())
    base = BASE.read_text()
    lines = base.splitlines()
    assert lines[0] == ",".join(f"x{i + 1}" for i in range(96)) and lines[1] == "3"
    assert len("\n".join(lines[2:]).strip().split(",\n")) == 176
    assert len(SIX_PREFIX) == 81 and SIX_PREFIX[0] == "1"
    fixes: list[dict[str, Any]] = []
    matrix = []
    augmented = []
    for cell, digit in enumerate(SIX_PREFIX):
        form = {
            int(v): c
            for v, c in model["original_color_linear_forms"][str(cell)].items()
        }
        assert form.get(95) == 1
        p = {1 << (4 * v): c for v, c in form.items()}
        if int(digit):
            p[0] = -int(digit) % 3
        fixes.append(
            {
                "original_cell": cell,
                "color": int(digit),
                "linear_form": form,
                "polynomial": expression(p),
            }
        )
        row = [form.get(v, 0) for v in range(96)]
        matrix.append(row)
        augmented.append([*row, int(digit)])
    assert fixes[0]["linear_form"] == {95: 1} and fixes[0]["polynomial"] == "2+x96"
    assert field_rank(matrix) == field_rank(augmented) == 80
    source = (
        base.rstrip("\n")
        + ",\n"
        + ",\n".join(fix["polynomial"] for fix in fixes)
        + "\n"
    )
    assert source.startswith(base.rstrip("\n") + ",\n")
    assert len("\n".join(source.splitlines()[2:]).strip().split(",\n")) == 257
    STEM.with_suffix(".ms").write_text(source)
    STEM.with_suffix(".fixes.json").write_text(json.dumps(fixes, indent=2) + "\n")
    command = [
        str(BINARY.resolve()),
        "-g",
        "1",
        "-l",
        "2",
        "-t",
        "1",
        "-r",
        "1",
        "-c",
        "0",
        "-v",
        "2",
        "-m",
        "16",
        "-f",
        str(STEM.with_suffix(".ms")),
        "-o",
        str(STEM.with_suffix(".basis")),
    ]
    record: dict[str, Any] = {
        "status": "RUNNING",
        "scope": "completions of a fixed81-original-cell prefix; not unrestricted",
        "prime": 3,
        "variables": 96,
        "generators": 257,
        "prefix": SIX_PREFIX,
        "fixed_original_cell_count": 81,
        "fixed_original_apex": 1,
        "offset_fixed_to": 1,
        "original_color_fix_rule": "z_cell=a+d_cell, including offset in every appended equation",
        "prefix_fix_coefficient_rank": 80,
        "prefix_fix_augmented_rank": 80,
        "base_generator_count": 176,
        "base_input_sha256": BASE_SHA,
        "model_sha256": MODEL_SHA,
        "input_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "executable_sha256": BINARY_SHA,
        "command": command,
        "threads": 1,
        "linear_algebra": "exact sparse (-l2)",
        "max_pairs": 16,
        "child_timeout_seconds": 30,
        "outer_timeout_seconds": 60,
        "memory_limit_bytes": 2 * 1024**3,
        "count_divisor": 1,
        "count_multiplier": 1,
        "extension_variable": False,
        "expected_dimension_decimal": "6",
        "basis_complete": False,
    }
    save_result(record)
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = ":".join(
        str(HERE / p)
        for p in ("exact_msolve_tools/usr/lib", "exact_algebra_backend_root/usr/lib")
    )
    started = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    with STEM.with_suffix(".log").open("x") as log:
        try:
            process = subprocess.run(
                command,
                stdout=log,
                stderr=subprocess.STDOUT,
                timeout=30,
                preexec_fn=limits,
                env=env,
                check=False,
            )
            record["returncode"] = process.returncode
            record["status"] = "BACKEND_ERROR"
        except subprocess.TimeoutExpired:
            record["status"] = "INCOMPLETE_TIMEOUT"
    record["child_wall_seconds"] = time.monotonic() - started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    record["child_cpu_seconds"] = (
        after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime
    )
    log = STEM.with_suffix(".log").read_text(errors="replace")
    record["export_marker_count"] = sum(
        line.strip() == "MSOLVE_PRIME_GB_EXPORT_COMPLETE" for line in log.splitlines()
    )
    record["error_diagnostics"] = [
        line
        for line in log.splitlines()
        if re.search(
            r"\berror\b|out of memory|cannot allocate|segmentation|aborted|allocation failed|bad_alloc|assertion|\bfatal\b",
            line,
            re.IGNORECASE,
        )
    ]
    record["log_sha256"] = digest(STEM.with_suffix(".log"))
    save_result(record)
    if (
        record.get("returncode") == 0
        and record["export_marker_count"] == 1
        and not record["error_diagnostics"]
    ):
        try:
            basis = STEM.with_suffix(".basis").read_text()
            leading = parse_leading(
                basis, 96, 3
            )  # strict complete header and payload audit
            record.update(
                basis_complete=True,
                basis_size=len(leading),
                basis_sha256=digest(STEM.with_suffix(".basis")),
            )
            leading_record = {
                "format": "leading-monomial-ideal-v1",
                "variables": 96,
                "standard_basis_complete": True,
                "leading_monomials": leading,
                "provenance": {
                    "backend": "reviewed6b msolve exact prime-field F4",
                    "input_sha256": record["input_sha256"],
                    "executable_sha256": BINARY_SHA,
                    "basis_sha256": record["basis_sha256"],
                    "scope": record["scope"],
                    "count_divisor": 1,
                },
            }
            STEM.with_suffix(".leading.json").write_text(
                json.dumps(leading_record, indent=2) + "\n"
            )
            first, first_stats = monomial_dimension(leading, 96, seconds=10)
            second_stats = {}
            second = count_standard_monomials(
                leading,
                96,
                standard_basis_complete=True,
                max_states=100000,
                stats=second_stats,
            )
            assert first == second == 6, (first, second)
            record["status"] = "COMPLETE_VERIFIED"
            record.update(
                dimension_decimal=str(first),
                independent_dimension_decimal=str(second),
                board_count_decimal=str(first),
                monomial_counter=first_stats,
                independent_counter=second_stats,
                strict_header_and_payload_verified=True,
            )
        except (
            AssertionError,
            ValueError,
            OSError,
            RuntimeError,
            MemoryError,
            RecursionError,
        ) as error:
            record["status"] = "POSTPROCESS_ERROR"
            record["postprocess_error"] = f"{type(error).__name__}: {error}"
    record["total_worker_seconds"] = time.monotonic() - started
    save_result(record)
    print(json.dumps(record), flush=True)
    return 0 if record["status"] == "COMPLETE_VERIFIED" else 1


def outer():
    outer_path = HERE / "exact_f3_translation_six.outer.json"
    log_path = HERE / "exact_f3_translation_six.outer.log"
    if outer_path.exists() or log_path.exists():
        raise ValueError("refusing to overwrite outer artifacts")
    command = [sys.executable, str(Path(__file__).resolve()), "--child"]
    started = time.monotonic()
    record: dict[str, Any] = {
        "command": command,
        "timeout_seconds": 60,
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
    if STEM.with_suffix(".json").exists():
        print(STEM.with_suffix(".json").read_text())
    return 0 if record["status"] == "COMPLETE" else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--child", action="store_true")
    args = parser.parse_args()
    raise SystemExit(worker() if args.child else outer())


if __name__ == "__main__":
    main()
