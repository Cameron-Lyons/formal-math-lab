#!/usr/bin/env python3
"""Compare completed bases against the preserved export-only msolve build."""

import hashlib
import json
import os
import re
import resource
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
EXPERIMENTS = ROOT.parent
sys.path.insert(0, str(EXPERIMENTS))
from exact_algebra_backend import monomial_dimension  # noqa: E402
from exact_msolve_backend import definitions, parse_leading  # noqa: E402
from exact_standard_monomials import (  # noqa: E402
    MissingPurePowerBounds,
    count_standard_monomials,
)

SIX_PREFIX = (
    "100011101011000101010011112112211212021201221022121202020220010222002102100022222"
)


def execute(name, kind, text, mode, seconds=20, la=2):
    executable = (
        ROOT if kind == "selective" else EXPERIMENTS / "exact_msolve_patched_tools"
    ) / "msolve"
    stem = ROOT / (name + "_" + kind + "_g" + str(mode))
    source, basis = stem.with_suffix(".ms"), stem.with_suffix(".basis")
    if source.exists() or basis.exists():
        raise ValueError("refusing to replace a prior test: " + str(stem))
    source.write_text(text)
    command = [
        str(executable),
        "-f",
        str(source),
        "-o",
        str(basis),
        "-g",
        str(mode),
        "-l",
        str(la),
        "-t",
        "1",
        "-r",
        "1",
        "-c",
        "0",
        "-v",
        "2",
    ]
    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = str(EXPERIMENTS / "exact_algebra_backend_root/usr/lib")

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (2048 * 1024**2, 2048 * 1024**2))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    timed_out = False
    try:
        process = subprocess.run(
            command,
            text=True,
            capture_output=True,
            env=env,
            preexec_fn=limits,
            timeout=seconds,
            check=False,
        )
        log, code = process.stdout + process.stderr, process.returncode
    except subprocess.TimeoutExpired as error:
        timed_out, code = True, None
        log = (
            (error.stdout or b"").decode()
            if isinstance(error.stdout, bytes)
            else (error.stdout or "")
        )
        log += (
            (error.stderr or b"").decode()
            if isinstance(error.stderr, bytes)
            else (error.stderr or "")
        )
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    stem.with_suffix(".log").write_text(log)
    data = basis.read_text() if basis.exists() else ""
    events = [
        dict(
            zip(
                ("nonpivot", "referenced", "inserted", "basis_capacity"),
                map(int, m),
                strict=False,
            )
        )
        for m in re.findall(
            r"MSOLVE_PROMOTION_COLUMNS nonpivot=(\d+) referenced=(\d+) "
            r"inserted=(\d+) basis_capacity=(\d+)",
            log,
        )
    ]
    record = {
        "name": name,
        "kind": kind,
        "mode": mode,
        "command": command,
        "returncode": code,
        "timed_out": timed_out,
        "memory_mb": 2048,
        "timeout_seconds": seconds,
        "wall_seconds": time.monotonic() - start,
        "cpu_seconds": after.ru_utime
        + after.ru_stime
        - before.ru_utime
        - before.ru_stime,
        "marker_count": sum(
            line.strip() == "MSOLVE_PRIME_GB_EXPORT_COMPLETE"
            for line in log.splitlines()
        ),
        "error_diagnostics": [
            line
            for line in log.splitlines()
            if re.search(
                r"\berror\b|out of memory|cannot allocate|segmentation|aborted",
                line,
                re.IGNORECASE,
            )
        ],
        "basis_sha256": hashlib.sha256(data.encode()).hexdigest(),
        "input_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "basis_file": str(basis),
        "promotion_events": events,
    }
    stem.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")
    assert (
        code == 0
        and not timed_out
        and record["marker_count"] == 1
        and not record["error_diagnostics"]
    ), record
    return record, data


def main():
    fixtures = [
        ("domain", 1, ["x1^3-1"], 3),
        ("domain_pair", 2, ["x1^3-1", "x2^3-1"], 9),
        ("root_sum", 3, ["x1^3-1", "x2^3-1", "x3^3-1", "x1+x2+x3"], 6),
        ("mixed", 2, ["x1^3-1", "x2^3-1", "x1*x2-1"], 3),
        (
            "mixed_chain",
            4,
            [f"x{i}^3-1" for i in range(1, 5)] + ["x1*x2-x3", "x2*x3-x4"],
            9,
        ),
        ("unit", 1, ["x1^3-1", "1"], 0),
        ("positive_dimension", 2, ["x1"], None),
    ]
    cases = []
    for name, n, equations, expected in fixtures:
        text = (
            ",".join(f"x{i + 1}" for i in range(n))
            + "\n29\n"
            + ",\n".join(equations)
            + "\n"
        )
        cases.append(
            (
                name,
                text,
                {"variables": n, "prime": 29, "count_divisor": 1},
                expected,
                20,
            )
        )
    text, metadata = definitions(prime=29, prefix=SIX_PREFIX)
    assert metadata["variables"] == 20 and metadata["count_divisor"] == 2
    cases.append(("six_fiber", text, metadata, 12, 90))
    results: list[dict[str, Any]] = []
    for name, text, metadata, expected, seconds in cases:
        for mode in (1, 2):
            old, old_text = execute(name, "baseline", text, mode, seconds)
            new, new_text = execute(name, "selective", text, mode, seconds)
            assert old_text == new_text, (name, mode, "basis bytes differ")
            if mode == 1:
                leading = parse_leading(
                    new_text, metadata["variables"], metadata["prime"]
                )
                if expected is None:
                    try:
                        count_standard_monomials(
                            leading, metadata["variables"], standard_basis_complete=True
                        )
                    except MissingPurePowerBounds:
                        pass
                    else:
                        raise AssertionError(
                            "positive-dimensional ideal accepted as finite"
                        )
                else:
                    a = monomial_dimension(leading, metadata["variables"])[0]
                    b = count_standard_monomials(
                        leading, metadata["variables"], standard_basis_complete=True
                    )
                    assert a == b == expected, (name, a, b, expected)
            results.append(
                {
                    "fixture": name,
                    "mode": mode,
                    "exports_byte_identical": True,
                    "expected_quotient_dimension": None
                    if expected is None
                    else str(expected),
                    "count_divisor": metadata["count_divisor"],
                    "runs": [old, new],
                }
            )
            print(
                name,
                mode,
                "PASS",
                "promotion events",
                len(new["promotion_events"]),
                flush=True,
            )
    all_events = [
        event
        for result in results
        for run in result["runs"]
        if run["kind"] == "selective"
        for event in run["promotion_events"]
    ]
    assert any(event["referenced"] < event["nonpivot"] for event in all_events), (
        "optimization not exercised"
    )
    report = {
        "status": "PASS",
        "complete_basis_comparisons": len(results),
        "results": results,
        "unused_columns_skipped_in_validation": True,
        "largest_nonpivot_to_referenced": max(
            all_events, key=lambda e: e["nonpivot"] - e["referenced"]
        ),
    }
    (ROOT / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))


if __name__ == "__main__":
    main()
