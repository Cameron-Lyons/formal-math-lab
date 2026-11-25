#!/usr/bin/env python3
"""Review the sole F3 gate extension and complete small independent bases."""

import hashlib
import itertools
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

HERE = Path(__file__).resolve().parent
SOURCE_NAME = "msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2"


def main():
    baseline_root = HERE / "exact_msolve_staged_promotion_tools"
    candidate_root = HERE / "exact_msolve_staged_f3_tools"
    baseline, candidate = baseline_root / "msolve", candidate_root / "msolve"
    old_source = baseline_root / SOURCE_NAME / "src"
    new_source = candidate_root / SOURCE_NAME / "src"
    old_files = {p.relative_to(old_source) for p in old_source.rglob("*.c")}
    new_files = {p.relative_to(new_source) for p in new_source.rglob("*.c")}
    assert old_files == new_files
    changed = [
        p
        for p in sorted(old_files)
        if (old_source / p).read_bytes() != (new_source / p).read_bytes()
    ]
    assert changed == [Path("neogb/convert.c")]
    old = (old_source / changed[0]).read_text()
    new = (new_source / changed[0]).read_text()
    target = "if (st->fc == 2 && st->laopt == 2 && st->nthrds == 1 &&"
    assert old.count(target) == 1
    assert (
        old.replace(
            target,
            "if ((st->fc == 2 || st->fc == 3) && st->laopt == 2 && st->nthrds == 1 &&",
        )
        == new
    )
    assert (
        hashlib.sha256((new_source / "neogb/hash.c").read_bytes()).hexdigest()
        == "8ff90c83d8decbec184c023cc71301a40273f9dfb2d6566e924b488b121c2f98"
    )
    output = HERE / "exact_msolve_staged_f3_review_runs"
    output.mkdir(exist_ok=False)

    def fields(n):
        return [f"x{i + 1}^3+2*x{i + 1}" for i in range(n)]

    fixtures = [
        ("field-domains", 4, fields(4), True),
        ("quadratic-extension", 1, ["x1^2+1"], False),
        ("signed-sum", 3, [*fields(3), "x1+2*x2+x3"], True),
        ("nonzero-product", 3, [*fields(3), "x1*x2*x3+2"], True),
        ("mixed-chain", 4, [*fields(4), "x1*x2+2*x3", "x2*x3+2*x4"], True),
        ("cycle", 3, ["x1^2+2*x2", "x2^2+2*x3", "x3^2+2*x1"], False),
        ("four-sum", 4, [*fields(4), "x1+x2+x3+x4"], True),
        ("dense-quadratic", 3, [*fields(3), "1+x1*x2+2*x1*x3+x2*x3"], True),
        ("quadratic-pair", 3, [*fields(3), "x1*x2+2*x3^2", "x1^2*x2^2+2*x3"], True),
        ("unit", 1, ["x1^3+2*x1", "x1", "x1+1"], True),
        ("nonradical", 2, ["x1^3", "x2^2"], False),
        (
            "dense-chain",
            4,
            [*fields(4), "x1*x2+x2*x3+2*x3*x4+1", "x1^2+2*x2*x4+x3+1"],
            True,
        ),
    ]
    env = dict(
        os.environ, LD_LIBRARY_PATH=str(HERE / "exact_algebra_backend_root/usr/lib")
    )

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    reports: list[dict[str, Any]] = []
    for name, variables, equations, field_domain in fixtures:
        input_path = output / (name + ".ms")
        input_path.write_text(
            ",".join(f"x{i + 1}" for i in range(variables))
            + "\n3\n"
            + ",\n".join(equations)
            + "\n"
        )
        original = [parse_polynomial(e, variables, 3) for e in equations]
        expected = buchberger(original, 3)
        assert all(not reduce_polynomial(p, expected, 3) for p in original)
        dimension = count_standard_monomials(
            [leading(p) for p in expected], variables, standard_basis_complete=True
        )
        direct_count = None
        if field_domain:

            def value(poly, point):
                total = 0
                for term, c in poly.items():
                    v = c
                    for x, e in zip(point, term, strict=False):
                        v = v * pow(x, e, 3) % 3
                    total = (total + v) % 3
                return total

            direct_count = sum(
                all(value(p, point) == 0 for p in original)
                for point in itertools.product(range(3), repeat=variables)
            )
            assert dimension == direct_count
        runs = []
        for label, executable in [("baseline", baseline), ("candidate", candidate)]:
            basis_path = output / (name + "_" + label + ".basis")
            command = [
                str(executable),
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
            completed = subprocess.run(
                command,
                capture_output=True,
                text=True,
                timeout=10,
                env=env,
                preexec_fn=limits,
                check=False,
            )
            log = completed.stdout + completed.stderr
            (output / (name + "_" + label + ".log")).write_text(log)
            assert completed.returncode == 0, (name, label, log[-2000:])
            assert log.splitlines().count("MSOLVE_PRIME_GB_EXPORT_COMPLETE") == 1
            assert not re.search(
                r"\berror\b|out of memory|cannot allocate|segmentation",
                log,
                re.IGNORECASE,
            )
            assert "MSOLVE_F2_BITSET rows=" not in log
            assert parse_full_basis(basis_path.read_text(), variables, 3) == expected
            runs.append(
                {
                    "label": label,
                    "command": command,
                    "basis_sha256": hashlib.sha256(basis_path.read_bytes()).hexdigest(),
                    "staging_rounds": log.count("MSOLVE_SYMBOLIC_STAGING old_load="),
                    "returncode": completed.returncode,
                }
            )
        assert runs[0]["basis_sha256"] == runs[1]["basis_sha256"]
        assert runs[0]["staging_rounds"] == 0
        reports.append(
            {
                "name": name,
                "variables": variables,
                "generators": len(equations),
                "quotient_dimension_decimal": str(dimension),
                "direct_F3_count": direct_count,
                "complete_basis_matches_python": True,
                "byte_identical_to_prior_build": True,
                "runs": runs,
            }
        )
    result = {
        "status": "PASS",
        "characteristic": 3,
        "fixtures": len(reports),
        "full_basis_comparisons": 2 * len(reports),
        "sole_source_change": "convert.c caller gate permits characteristic3 in addition to2",
        "identical_C_source_files": len(old_files) - 1,
        "hash_helper_identical": True,
        "candidate_sha256": hashlib.sha256(candidate.read_bytes()).hexdigest(),
        "baseline_sha256": hashlib.sha256(baseline.read_bytes()).hexdigest(),
        "patch_sha256": hashlib.sha256(
            (candidate_root / "enable-f3-staging.patch").read_bytes()
        ).hexdigest(),
        "staging_rounds": sum(row["runs"][1]["staging_rounds"] for row in reports),
        "F2_bitset_rounds": 0,
        "direct_F3_enumeration_fixtures": sum(
            row["direct_F3_count"] is not None for row in reports
        ),
        "full_board_solver_runs": 0,
        "memory_limit_bytes": 2 * 1024**3,
        "results": reports,
    }
    assert result["staging_rounds"] > 0
    (HERE / "exact_msolve_staged_f3_review_results.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps({k: v for k, v in result.items() if k != "results"}, indent=2))


if __name__ == "__main__":
    main()
