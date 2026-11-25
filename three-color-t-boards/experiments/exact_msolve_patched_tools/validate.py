#!/usr/bin/env python3
"""Compare patched/stock exports without running a T-board problem."""

import hashlib
import json
import os
import resource
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXPERIMENTS = ROOT.parent
sys.path.insert(0, str(EXPERIMENTS))
from exact_algebra_backend import monomial_dimension  # noqa: E402
from exact_msolve_backend import parse_leading  # noqa: E402
from exact_standard_monomials import (  # noqa: E402
    MissingPurePowerBounds,
    count_standard_monomials,
)


def execute(name, kind, n, equations, prime=29, mode=1, seconds=5, memory_mb=2048):
    executable = (
        ROOT / "msolve"
        if kind == "patched"
        else EXPERIMENTS / "exact_msolve_tools/msolve"
    )
    stem = ROOT / (name + "_" + kind + "_g" + str(mode))
    source = stem.with_suffix(".ms")
    basis = stem.with_suffix(".basis")
    source.write_text(
        ",".join(f"x{i + 1}" for i in range(n))
        + "\n"
        + str(prime)
        + "\n"
        + ",\n".join(equations)
        + "\n"
    )
    if basis.exists():
        basis.unlink()
    command = [
        str(executable),
        "-f",
        str(source),
        "-o",
        str(basis),
        "-g",
        str(mode),
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
    ]
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = (
        str(EXPERIMENTS / "exact_msolve_tools/usr/lib")
        + ":"
        + str(EXPERIMENTS / "exact_algebra_backend_root/usr/lib")
    )

    def limits():
        resource.setrlimit(
            resource.RLIMIT_AS, (memory_mb * 1024**2, memory_mb * 1024**2)
        )
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    timeout = False
    try:
        result = subprocess.run(
            command,
            text=True,
            capture_output=True,
            env=env,
            preexec_fn=limits,
            timeout=seconds,
            check=False,
        )
        log = result.stdout + result.stderr
        code = result.returncode
    except subprocess.TimeoutExpired as error:
        timeout = True
        code = None
        log = (
            (error.stdout or b"").decode()
            if isinstance(error.stdout, bytes)
            else (error.stdout or "")
        )
        log += (
            error.stderr.decode()
            if isinstance(error.stderr, bytes)
            else (error.stderr or "")
        )
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    stem.with_suffix(".log").write_text(log)
    data = basis.read_text() if basis.exists() else ""
    record = {
        "name": name,
        "kind": kind,
        "mode": mode,
        "command": command,
        "returncode": code,
        "timed_out": timeout,
        "memory_mb": memory_mb,
        "wall_seconds": time.monotonic() - start,
        "cpu_seconds": after.ru_utime
        + after.ru_stime
        - before.ru_utime
        - before.ru_stime,
        "marker_count": log.count("MSOLVE_PRIME_GB_EXPORT_COMPLETE"),
        "basis_sha256": hashlib.sha256(data.encode()).hexdigest(),
        "basis_file": str(basis),
    }
    return record, data


def main():
    fixtures = [
        ("domain", 1, ["x1^3-1"], 3),
        ("domain_pair", 2, ["x1^3-1", "x2^3-1"], 9),
        ("root_sum", 3, ["x1^3-1", "x2^3-1", "x3^3-1", "x1+x2+x3"], 6),
        ("mixed", 2, ["x1^3-1", "x2^3-1", "x1*x2-1"], 3),
        ("unit", 1, ["x1^3-1", "1"], 0),
        ("positive_dimension", 2, ["x1"], None),
    ]
    results = []
    for name, n, equations, expected in fixtures:
        for mode in (1, 2):
            records = []
            exports = []
            for kind in ("stock", "patched"):
                record, data = execute(name, kind, n, equations, mode=mode)
                assert record["returncode"] == 0 and not record["timed_out"], record
                assert record["marker_count"] == int(kind == "patched"), record
                records.append(record)
                exports.append(data)
            assert exports[0] == exports[1], (name, mode)
            if mode == 1:
                leading = parse_leading(exports[1], n, 29)
                if expected is None:
                    try:
                        count_standard_monomials(
                            leading, n, standard_basis_complete=True
                        )
                    except MissingPurePowerBounds:
                        pass
                    else:
                        raise AssertionError(
                            "positive-dimensional fixture accepted as finite"
                        )
                else:
                    assert (
                        monomial_dimension(leading, n)[0]
                        == count_standard_monomials(
                            leading, n, standard_basis_complete=True
                        )
                        == expected
                    )
            results.append(
                {
                    "fixture": name,
                    "mode": mode,
                    "exports_byte_identical": True,
                    "expected_dimension": None if expected is None else str(expected),
                    "runs": records,
                }
            )
    # The stock process is bounded because it enumerates the huge staircase after export.
    equations = [f"x{i + 1}^3-1" for i in range(100)]
    record, data = execute("hundred_cubics", "patched", 100, equations, seconds=10)
    assert (
        record["returncode"] == 0
        and record["marker_count"] == 1
        and not record["timed_out"]
    ), record
    leading = parse_leading(data, 100, 29)
    expected = 3**100
    assert (
        monomial_dimension(leading, 100)[0]
        == count_standard_monomials(leading, 100, standard_basis_complete=True)
        == expected
    )
    stock, stock_data = execute("hundred_cubics", "stock", 100, equations, seconds=2)
    assert stock_data == data, "stock/patched leading exports differ for100 cubics"
    assert stock["returncode"] != 0 or stock["timed_out"], (
        "unexpected stock staircase completion"
    )
    results.append(
        {
            "fixture": "hundred_cubics",
            "expected_dimension": str(expected),
            "exports_byte_identical": True,
            "patched_completed_without_staircase": True,
            "stock_failed_after_matching_export": True,
            "runs": [stock, record],
        }
    )
    result = {"status": "PASS", "small_export_comparisons": 12, "results": results}
    (ROOT / "validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {
                "status": "PASS",
                "small_export_comparisons": 12,
                "hundred_cubic_dimension": str(expected),
                "hundred_cubics_patched": record,
                "hundred_cubics_stock": stock,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
