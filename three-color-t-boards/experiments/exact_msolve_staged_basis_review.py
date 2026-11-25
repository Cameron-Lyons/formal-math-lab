#!/usr/bin/env python3
"""Independent complete F2 basis checks for staged symbolic promotion."""

import hashlib
import json
import os
import re
import resource
import subprocess
from pathlib import Path
from typing import Any

from exact_msolve_sparse_review import (
    buchberger,
    leading,
    parse_full_basis,
    parse_polynomial,
    reduce_polynomial,
)
from exact_standard_monomials import count_standard_monomials

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / "experiments"


def main():
    output = HERE / "exact_msolve_staged_basis_review_runs"
    output.mkdir(exist_ok=False)
    baseline = HERE / "exact_msolve_f2_bitset_tools/msolve"
    candidate = HERE / "exact_msolve_staged_promotion_tools/msolve"

    def cubes(n):
        return [f"x{i + 1}^3+1" for i in range(n)]

    fixtures = [
        ("cubic-domains", 3, cubes(3), 27),
        ("quadratic-extension", 1, ["x1^2+x1+1"], 2),
        ("root-sum", 3, [*cubes(3), "x1+x2+x3"], 6),
        ("root-product", 3, [*cubes(3), "x1*x2*x3+1"], 9),
        ("mixed-chain", 4, [*cubes(4), "x1*x2+x3", "x2*x3+x4"], 9),
        ("cycle", 3, ["x1^2+x2", "x2^2+x3", "x3^2+x1"], 8),
        ("four-sum", 4, [*cubes(4), "x1+x2+x3+x4"], 21),
        ("dense-quadratic", 3, [*cubes(3), "1+x1*x2+x1*x3+x2*x3"], None),
        ("frobenius-pair", 3, [*cubes(3), "x1*x2+x3^2", "x1^2*x2^2+x3"], 9),
        ("unit", 1, [*cubes(1), "x1"], 0),
        ("nonradical", 2, ["x1^3", "x2^2"], 6),
        ("dense-chain", 4, [*cubes(4), "x1*x2+x2*x3+x3*x4+1", "x1^2+x2*x4+x3+1"], None),
    ]
    env = dict(
        os.environ, LD_LIBRARY_PATH=str(HERE / "exact_algebra_backend_root/usr/lib")
    )

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    reports: list[dict[str, Any]] = []
    for name, variables, equations, wanted_count in fixtures:
        input_path = output / (name + ".ms")
        input_path.write_text(
            ",".join(f"x{i + 1}" for i in range(variables))
            + "\n2\n"
            + ",\n".join(equations)
            + "\n"
        )
        original = [parse_polynomial(equation, variables, 2) for equation in equations]
        expected = buchberger(original, 2)
        assert all(
            not reduce_polynomial(polynomial, expected, 2) for polynomial in original
        )
        dimension = count_standard_monomials(
            [leading(poly) for poly in expected],
            variables,
            standard_basis_complete=True,
        )
        if wanted_count is not None:
            assert dimension == wanted_count, (name, dimension, wanted_count)
        runs = []
        for label, executable in [("baseline", baseline), ("candidate", candidate)]:
            basis_path = output / (name + "_" + label + ".basis")
            command = [
                str(executable.resolve()),
                "-g",
                "2",
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
                "-s",
                "4",
                "-f",
                str(input_path),
                "-o",
                str(basis_path),
            ]
            result = subprocess.run(
                command,
                text=True,
                capture_output=True,
                timeout=10,
                env=env,
                preexec_fn=limits,
                check=False,
            )
            log = result.stdout + result.stderr
            (output / (name + "_" + label + ".log")).write_text(log)
            assert result.returncode == 0, (name, label, result.returncode, log[-1000:])
            assert log.splitlines().count("MSOLVE_PRIME_GB_EXPORT_COMPLETE") == 1
            assert not re.search(
                r"\berror\b|out of memory|cannot allocate|segmentation",
                log,
                re.IGNORECASE,
            )
            actual = parse_full_basis(basis_path.read_text(), variables, 2)
            assert actual == expected, (name, label, actual, expected)
            runs.append(
                {
                    "label": label,
                    "command": command,
                    "basis_sha256": hashlib.sha256(basis_path.read_bytes()).hexdigest(),
                    "bitset_rounds": log.count("MSOLVE_F2_BITSET rows="),
                    "staging_rounds": log.count("MSOLVE_SYMBOLIC_STAGING old_load="),
                    "returncode": result.returncode,
                }
            )
        assert runs[0]["basis_sha256"] == runs[1]["basis_sha256"]
        reports.append(
            {
                "name": name,
                "variables": variables,
                "generators": len(equations),
                "quotient_dimension_decimal": str(dimension),
                "complete_basis_matches_python": True,
                "byte_identical_to_prior_build": True,
                "runs": runs,
            }
        )
    report = {
        "status": "PASS",
        "characteristic": 2,
        "fixtures": len(reports),
        "full_basis_comparisons": 2 * len(reports),
        "bitset_rounds": sum(item["runs"][1]["bitset_rounds"] for item in reports),
        "staging_rounds": sum(item["runs"][1]["staging_rounds"] for item in reports),
        "candidate_sha256": hashlib.sha256(candidate.read_bytes()).hexdigest(),
        "baseline_sha256": hashlib.sha256(baseline.read_bytes()).hexdigest(),
        "full_board_solver_runs": 0,
        "memory_limit_bytes": 2 * 1024**3,
        "results": reports,
    }
    assert report["staging_rounds"] > 0, "Candidate did not exercise staging"
    (HERE / "exact_msolve_staged_basis_review_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))


if __name__ == "__main__":
    main()
