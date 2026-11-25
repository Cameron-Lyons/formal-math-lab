#!/usr/bin/env python3
"""Bounded natural-F3 fixed-fiber regression; never runs the full model."""

import hashlib
import json
from pathlib import Path

from validate import (
    count_standard_monomials,
    execute,
    monomial_dimension,
    parse_leading,
)

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "exact_native_field_probe_runs/ternary_six.ms"


def main():
    text = SOURCE.read_text()
    lines = text.splitlines()
    assert len(lines[0].split(",")) == 19 and lines[1].strip() == "3"
    assert len("".join(lines[2:]).split(",")) == 99
    results = []
    for mode in (1, 2):
        old, old_text = execute("natural_f3_six", "baseline", text, mode, seconds=30)
        new, new_text = execute("natural_f3_six", "selective", text, mode, seconds=30)
        assert old_text == new_text
        counts = []
        if mode == 1:
            for basis in (old_text, new_text):
                leading = parse_leading(basis, 19, 3)
                a = monomial_dimension(leading, 19)[0]
                b = count_standard_monomials(leading, 19, standard_basis_complete=True)
                assert a == b == 6
                counts.append(
                    {
                        "quotient_dimension": str(a),
                        "independent_dimension": str(b),
                        "board_count": "6",
                        "divisor": 1,
                    }
                )
        assert not new["staging_events"], "current frozen gate is F2-only"
        results.append(
            {
                "mode": mode,
                "status": "COMPLETE",
                "exports_byte_identical": True,
                "runs": [old, new],
                "counts": counts,
            }
        )
    report = {
        "status": "PASS",
        "model": "root-audited natural F3 fixed nine-row six-completion fiber",
        "variables": 19,
        "generators": 99,
        "expected_quotient_dimension": "6",
        "count_divisor": 1,
        "full_model_solver_runs": 0,
        "scope_note": "F3 uses the old path in this frozen F2-gated sixth build",
        "source": str(SOURCE),
        "source_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "results": results,
    }
    (ROOT / "f3_validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(
        "PASS F3 six-fiber: g1/g2 byte-identical; both exact counts6, divisor1; staging gate off"
    )


if __name__ == "__main__":
    main()
