#!/usr/bin/env python3
import hashlib
import json
import os
import resource
import subprocess
import time
from pathlib import Path

R = Path(__file__).resolve().parent
BASE = "x1\n3\nx1^3-x1\n"


def run(name, text=BASE, extra=()):
    p = R / ("reject_" + name)
    assert not p.with_suffix(".ms").exists()
    p.with_suffix(".ms").write_text(text)
    cmd = [
        str(R / "msolve"),
        "-f",
        str(p.with_suffix(".ms")),
        "-o",
        str(p.with_suffix(".basis")),
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
        *extra,
    ]

    def limit():
        resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    start = time.monotonic()
    q = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=10,
        preexec_fn=limit,
        env=dict(
            os.environ,
            LD_LIBRARY_PATH=str(R.parent / "exact_algebra_backend_root/usr/lib"),
        ),
        check=False,
    )
    log = q.stdout + q.stderr
    p.with_suffix(".log").write_text(log)
    assert (
        q.returncode != 0
        and "Error:" in log
        and "MSOLVE_PRIME_GB_EXPORT_COMPLETE" not in log
    ), (name, q)
    assert (
        not p.with_suffix(".basis").exists() or not p.with_suffix(".basis").read_bytes()
    ), name
    return {
        "name": name,
        "returncode": q.returncode,
        "command": cmd,
        "wall_seconds": time.monotonic() - start,
        "diagnostic": next(x for x in log.splitlines() if "Error:" in x),
        "input_sha256": hashlib.sha256(text.encode()).hexdigest(),
    }


def main():
    cases = [
        ("exponent_256", BASE.replace("^3", "^256")),
        ("exponent_2pow32_plus3", BASE.replace("^3", "^4294967299")),
        ("exponent_huge", BASE.replace("^3", "^9999999999999999999999999999")),
        ("negative_exponent", BASE.replace("^3", "^-1")),
        ("missing_exponent", BASE.replace("^3", "^")),
        ("coefficient_overflow", BASE.replace("x1^3", "4294967297*x1^3")),
        ("unknown_variable", BASE + " ,x2\n"),
        ("leading_zero_variable", BASE + " ,x01\n"),
        ("repeated_variable", BASE + " ,x1*x1\n"),
        ("noncanonical_header", BASE.replace("x1\n", "y\n", 1)),
        ("missing_domain", "x1\n3\nx1^2-x1\n"),
        ("wrong_domain_sign", "x1\n3\nx1^3+x1\n"),
        ("high_nondomain", BASE + ",x1^3+1\n"),
        ("field_two", BASE.replace("\n3\n", "\n2\n")),
        ("field_zero", BASE.replace("\n3\n", "\n0\n")),
        ("field_29", BASE.replace("\n3\n", "\n29\n")),
        ("empty_body", "x1\n3\n"),
        ("bad_term", BASE + ",x1**2\n"),
        ("trailing_comma", BASE + ",\n"),
        ("negative_variable", BASE + ",x-1\n"),
        ("fraction", BASE + ",1/2\n"),
    ]
    n = 128
    cases.append(
        ("variables128", ",".join(f"x{i}" for i in range(1, n + 1)) + "\n3\n1\n")
    )
    n = 127
    domains = ",".join(f"x{i}^3-x{i}" for i in range(1, n + 1))
    cases.append(
        (
            "degree381",
            ",".join(f"x{i}" for i in range(1, n + 1))
            + "\n3\n"
            + domains
            + ","
            + "*".join(f"x{i}^3" for i in range(1, n + 1))
            + "\n",
        )
    )
    results = [run(name, text) for name, text in cases]
    for name, extra in [
        ("signature", ["-q", "1"]),
        ("signature_clamped", ["-q", "999"]),
        ("normalform", ["-n", "1"]),
        ("saturation", ["-S"]),
        ("colon", ["-C"]),
        ("elimination", ["-e", "1"]),
        ("two_threads", ["-t", "2"]),
        ("la1", ["-l", "1"]),
        ("probabilistic_la", ["-l", "42"]),
        ("no_export", ["-g", "0"]),
        ("no_reduce", ["-r", "0"]),
        ("genericity", ["-c", "2"]),
        ("option_wrap", ["-t", "4294967297"]),
        ("negative_hash", ["-s", "-1"]),
        ("binary_input", ["-F", "missing"]),
        ("parametrization", ["-P", "1"]),
    ]:
        results.append(run(name, extra=extra))
    report = {
        "status": "PASS",
        "rejection_cases": len(results),
        "full_board_solver_runs": 0,
        "executable_sha256": hashlib.sha256((R / "msolve").read_bytes()).hexdigest(),
        "results": results,
    }
    (R / "guard_check.json").write_text(json.dumps(report, indent=2) + "\n")
    print("PASS", len(results), "parser/model/mode rejections")


if __name__ == "__main__":
    main()
