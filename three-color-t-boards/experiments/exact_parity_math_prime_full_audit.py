#!/usr/bin/env python3
"""Read-only audit of the exported full29-characteristic Singular instance."""

import hashlib
import json
import re
from collections import Counter
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
STEM = HERE / "exact_algebra_backend_full_prime29_all"


def main():
    script_path = STEM.with_suffix(".sing")
    raw = script_path.read_bytes()
    script = raw.decode()
    ring = "ring R=29,(" + ",".join(f"x{i + 1}" for i in range(100)) + "),dp;\n"
    assert script.startswith(ring + "ideal I=\n")
    definition, driver = script[len(ring + "ideal I=\n") :].split(";\n", 1)
    equations = definition.split(",\n")
    assert len(equations) == 180
    assert equations[:100] == [f"x{i + 1}^3-1" for i in range(100)]
    assert driver.startswith('option(redSB);\nprint("GB_STARTED");\nideal G=std(I);\n')
    assert "BASIS_IS_STANDARD=" in driver and "LM_COMPLETE" in driver
    assert "bigintvec H=hilb(G,2)" in driver
    assert not re.search(r"\bI\s*=", driver)
    assert not re.search(r"\bring\s", driver)

    # Construct geometry using centered horizontal coordinates independently
    # of the exporting generator's row-start formula.
    cells = {(r, x): r * r + x + r for r in range(10) for x in range(-r, r + 1)}
    windows = [
        (cells[r, x], cells[r + 1, x - 1], cells[r + 1, x], cells[r + 1, x + 1])
        for r in range(9)
        for x in range(-r, r + 1)
    ]
    assert len(set(windows)) == 81 and set(cells.values()) == set(range(100))
    exponents = [e for e in product(range(3), repeat=4) if any(e)]
    assert len(exponents) == 80
    parsed = []
    for expression, e in zip(equations[100:], exponents, strict=False):
        terms = Counter()
        for summand in expression.split("+"):
            factors = summand.split("*")
            assert factors.pop(0) == "1"
            pairs = []
            for factor in factors:
                match = re.fullmatch(r"x([1-9][0-9]*)(?:\^([12]))?", factor)
                assert match, factor
                pairs.append((int(match[1]) - 1, int(match[2] or 1)))
            assert len({cell for cell, _ in pairs}) == len(pairs)
            terms[tuple(sorted(pairs))] += 1
        expected = Counter(
            tuple(
                sorted(
                    (cell, power) for cell, power in zip(w, e, strict=False) if power
                )
            )
            for w in windows
        )
        assert terms == expected and len(terms) == 81 and set(terms.values()) == {1}
        parsed.append(terms)

    report = {
        "status": "PASS",
        "script": str(script_path),
        "script_sha256": hashlib.sha256(raw).hexdigest(),
        "field": "F29",
        "variables": 100,
        "cubic_domains": 100,
        "nonconstant_moments": 80,
        "moment_terms": sum(sum(p.values()) for p in parsed),
        "normalization_constraints": 0,
        "fixed_cells": 0,
        "count_multiplier": 1,
        "geometry_rebuilt_from_centered_coordinates": True,
        "no_basis_computation_performed_by_this_audit": True,
    }
    model_path = STEM.with_suffix(".model.json")
    if model_path.exists():
        data = json.loads(model_path.read_text())
        assert data["variables"] == 100 and data["coefficient_characteristic"] == 29
        assert data["prefix"] == [] and data["free_original_cells"] == list(range(100))
        assert data["all_nonconstant_moments"] is True
        assert [
            tuple(eq["role_exponents"]) for eq in data["moment_equations"]
        ] == exponents
        for eq, actual in zip(data["moment_equations"], parsed, strict=False):
            assert eq["rhs"] == [0, 0]
            assert all(term["coefficient"] == [1, 0] for term in eq["terms"])
            assert (
                Counter(
                    tuple(tuple(pair) for pair in term["monomial"])
                    for term in eq["terms"]
                )
                == actual
            )
        canonical = json.dumps(data, sort_keys=True).encode()
        report["canonical_model_sha256"] = hashlib.sha256(canonical).hexdigest()
    metadata_path = STEM.with_suffix(".json")
    if metadata_path.exists():
        result = json.loads(metadata_path.read_text())
        assert result["model"] == "prime-all:29" and result["field"] == "F29"
        assert result["variables"] == 100 and result["generators"] == 180
        assert result["prefix"] == "" and result["free_original_cells"] == list(
            range(100)
        )
        assert result["algorithm"] == "std" and result["ordering"] == "dp"
        assert result["memory_mb"] == 2048 and result["timeout_seconds"] == 90
        assert (
            "unrestricted_multiplier" not in result
            and "unrestricted_labeled_count" not in result
        )
        assert result["script_sha256"] == report["script_sha256"]
        if "canonical_model_sha256" in report:
            assert result["model_data_sha256"] == report["canonical_model_sha256"]
        report["backend_status"] = result["status"]
        if result["status"] in ("COMPLETE", "COMPLETE_FROM_LEADING_IDEAL"):
            count = result["quotient_dimension"]
            assert result["basis_complete"] is True
            assert (
                count
                == result["monomial_dimension"]
                == result["independent_monomial_dimension"]
            )
            assert result["dimension_decimal"] == str(count)
            if "hilbert_dimension" in result:
                assert result["hilbert_dimension"] == count
            # Necessary consequences of existing valid-board certificates and
            # the proven free palette/reflection action; not a substitute for
            # verifying the completed leading ideal.
            assert count >= 32155680 and count % 12 == 0
            report["reported_quotient_dimension_decimal"] = str(count)
            report["count_status"] = "REQUIRES_FINAL_LEADING_EXPORT_AUDIT"
        else:
            assert "quotient_dimension" not in result
            report["count_status"] = "NO_EXACT_COUNT"
            log = STEM.with_suffix(".log").read_text()
            assert "GB_COMPLETE" not in log and "LM_COMPLETE" not in log
            assert result["basis_complete"] is False
            assert not STEM.with_suffix(".leading.json").exists()
            report["failure_evidence"] = {
                "returncode": result.get("returncode"),
                "memory_exhaustion_message": "no more memory" in log,
                "standard_basis_completed": False,
                "leading_export_exists": False,
                "child_cpu_seconds": result["child_cpu_seconds"],
                "elapsed_seconds": result["elapsed_seconds"],
            }
    else:
        report["backend_status"] = "RUNNING_OR_NOT_RECORDED"
        report["count_status"] = "NO_EXACT_COUNT_AUDITED"
    out = HERE / "exact_parity_math_prime_full_audit.json"
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
