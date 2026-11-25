#!/usr/bin/env python3
"""Audit actual full msolve input; never invoke msolve or another basis engine."""

import hashlib
import json
import re
from collections import Counter
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
STEM = HERE / "exact_msolve_full_prime29_all"


def main():
    path = STEM.with_suffix(".ms")
    raw = path.read_bytes()
    lines = raw.decode().splitlines()
    assert lines[0] == ",".join(f"x{i + 1}" for i in range(100))
    assert lines[1] == "29"
    polynomials = "\n".join(lines[2:]).strip().split(",\n")
    assert len(polynomials) == 180
    assert polynomials[:100] == [f"x{i + 1}^3-1" for i in range(100)]

    # Independent centered coordinates: each top cell at horizontal x sits
    # above the lower triple x-1,x,x+1.
    cell = {(r, x): r * r + r + x for r in range(10) for x in range(-r, r + 1)}
    windows = [
        (cell[r, x], cell[r + 1, x - 1], cell[r + 1, x], cell[r + 1, x + 1])
        for r in range(9)
        for x in range(-r, r + 1)
    ]
    assert len(windows) == len(set(windows)) == 81
    assert set(cell.values()) == set(range(100))
    exponents = [e for e in product(range(3), repeat=4) if any(e)]
    for expression, e in zip(polynomials[100:], exponents, strict=False):
        actual = Counter()
        for summand in expression.split("+"):
            factors = summand.split("*")
            assert factors.pop(0) == "1"
            pairs = []
            for factor in factors:
                match = re.fullmatch(r"x([1-9][0-9]*)(?:\^([12]))?", factor)
                assert match, factor
                pairs.append((int(match[1]) - 1, int(match[2] or 1)))
            assert len({c for c, _ in pairs}) == len(pairs)
            actual[tuple(sorted(pairs))] += 1
        expected = Counter(
            tuple(sorted((c, p) for c, p in zip(window, e, strict=False) if p))
            for window in windows
        )
        assert actual == expected and len(actual) == 81 and set(actual.values()) == {1}

    report = {
        "status": "PASS",
        "scope": "unrestricted labeled ten-row ternary boards",
        "input_file": str(path),
        "input_sha256": hashlib.sha256(raw).hexdigest(),
        "field": "F29",
        "ordinary_polynomial_variables": 100,
        "cubic_domains": 100,
        "nonconstant_fourier_moments": 80,
        "moment_terms": 6480,
        "fixed_cells": 0,
        "normalization_constraints": 0,
        "count_divisor": 1,
        "count_multiplier": 1,
        "independently_rebuilt_centered_geometry": True,
        "solver_invoked_by_audit": False,
    }
    result_path = STEM.with_suffix(".json")
    if result_path.exists():
        result = json.loads(result_path.read_text())
        assert result["source_sha256"] == report["input_sha256"]
        assert result["scope"] == "full labeled boards" and result["prefix"] == ""
        assert (
            result["prime"] == 29
            and result["variables"] == 100
            and result["generators"] == 180
        )
        assert (
            result["free_board_variables"] == 100
            and result["extension_variable"] is False
        )
        assert result["count_divisor"] == 1 and result["moment_equations"] == 80
        assert result["ring_type"] == "ordinary polynomial ring"
        assert result["require_export_marker"] is True
        command = result["command"]
        assert (
            Path(command[0]).name == "msolve"
            and "exact_msolve_patched_tools" in command[0]
        )
        assert command[command.index("-l") + 1] == "2"
        assert command[command.index("-t") + 1] == "1"
        assert command[command.index("-m") + 1] == "256"
        assert result["timeout_seconds"] == 90 and result["memory_mb"] == 2048
        assert (
            result["executable_sha256"]
            == hashlib.sha256(Path(command[0]).read_bytes()).hexdigest()
        )
        report["backend_status"] = result["status"]
        report["basis_complete"] = result["basis_complete"]
        report["export_marker_count"] = result["export_marker_count"]
        report["leading_export_exists"] = STEM.with_suffix(".leading.json").exists()
        basis_path = STEM.with_suffix(".basis")
        report["basis_file_bytes"] = (
            basis_path.stat().st_size if basis_path.exists() else None
        )
        if result["status"] == "COMPLETE":
            assert result["basis_complete"] is True and result["returncode"] == 0
            assert (
                result["export_marker_count"] == 1 and not result["error_diagnostics"]
            )
            assert result["dimension_decimal"] == result["board_count_decimal"]
            count = int(result["board_count_decimal"])
            assert count >= 32155680 and count % 12 == 0
            report["reported_board_count_decimal"] = str(count)
            report["count_status"] = "REQUIRES_COMPLETED_LEADING_EXPORT_REVIEW"
        else:
            assert (
                "board_count_decimal" not in result
                and "dimension_decimal" not in result
            )
            report["count_status"] = "NO_EXACT_COUNT"
            report["returncode"] = result.get("returncode")
            report["child_cpu_seconds"] = result.get("child_cpu_seconds")
            report["child_wall_seconds"] = result.get("child_wall_seconds")
    else:
        report["backend_status"] = "NOT_YET_RECORDED"
        report["count_status"] = "NO_EXACT_COUNT_AUDITED"
    output = HERE / "exact_parity_math_msolve_audit.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
