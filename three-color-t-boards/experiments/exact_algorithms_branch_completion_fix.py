#!/usr/bin/env python3
"""Re-attest completed small fixtures after correcting a stale metadata flag.

No solver. Original metadata are preserved verbatim. Counts and actual-run
adapter hashes stay unchanged; current parser and both counters recheck the
existing completed exports before any correction is written.
"""

import hashlib
import json
from pathlib import Path

from exact_algebra_backend import monomial_dimension
from exact_msolve_backend import parse_leading
from exact_standard_monomials import count_standard_monomials

HERE = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    source = (HERE / "exact_msolve_backend.py").read_text()
    prior = source.replace(
        "metadata.update(basis_complete=True,standard_basis_complete=True,\n                            basis_size=",
        "metadata.update(basis_complete=True,basis_size=",
    )
    reviewed = json.loads(
        (HERE / "exact_algorithms_branch_adapter_review.json").read_text()
    )
    assert hashlib.sha256(prior.encode()).hexdigest() == reviewed["backend_sha256"]
    records = []
    for stem in ["exact_algorithms_sign_six"] + [
        f"exact_algorithms_branch_six_{k}" for k in range(4)
    ]:
        base = HERE / stem
        path = base.with_suffix(".json")
        backup = base.with_suffix(".pre_flag_fix.json")
        assert not backup.exists()
        raw = path.read_bytes()
        data = json.loads(raw)
        assert data["status"] == "COMPLETE" and data["basis_complete"] is True
        assert data["standard_basis_complete"] is False and data["returncode"] == 0
        assert data["export_marker_count"] == 1 and data["error_diagnostics"] == []
        assert sha(base.with_suffix(".ms")) == data["source_sha256"]
        assert sha(base.with_suffix(".log")) == data["log_sha256"]
        assert sha(base.with_suffix(".basis")) == data["basis_sha256"]
        log = base.with_suffix(".log").read_text()
        assert (
            sum(
                line.strip() == "MSOLVE_PRIME_GB_EXPORT_COMPLETE"
                for line in log.splitlines()
            )
            == 1
        )
        leading = parse_leading(base.with_suffix(".basis").read_text(), 97, 3)
        exported = json.loads(base.with_suffix(".leading.json").read_text())
        assert (
            exported["standard_basis_complete"] is True
            and exported["leading_monomials"] == leading
        )
        assert exported["provenance"]["input_sha256"] == data["source_sha256"]
        first, _ = monomial_dimension(leading, 97, seconds=10)
        second = count_standard_monomials(
            leading, 97, standard_basis_complete=True, max_states=100000
        )
        assert (
            str(first)
            == str(second)
            == data["dimension_decimal"]
            == data["board_count_decimal"]
        )
        backup.write_bytes(raw)
        correction = {
            "field": "standard_basis_complete",
            "before": False,
            "after": True,
            "reason": "inherited prepared-state flag was not updated by prior backend after strict completed-export parsing",
            "original_metadata_file": backup.name,
            "original_metadata_sha256": hashlib.sha256(raw).hexdigest(),
            "correction_method": "existing completed export reparsed; both exact integer counters re-agree; no solver rerun",
            "correction_script_sha256": sha(Path(__file__)),
            "correction_backend_sha256": sha(HERE / "exact_msolve_backend.py"),
        }
        data["standard_basis_complete"] = True
        data.setdefault("metadata_corrections", []).append(correction)
        path.write_text(json.dumps(data, indent=2) + "\n")
        records.append(
            {
                "file": path.name,
                "prior_metadata_sha256": correction["original_metadata_sha256"],
                "corrected_metadata_sha256": sha(path),
                "dimension_decimal": str(first),
                "basis_size": len(leading),
            }
        )
    report = {
        "status": "PASS",
        "scope": "metadata-only correction of completed small fixtures",
        "backend_change": "exactly add standard_basis_complete=True at the existing successful parse attestation",
        "previously_audited_backend_sha256": reviewed["backend_sha256"],
        "current_backend_sha256": sha(HERE / "exact_msolve_backend.py"),
        "records": records,
        "solver_runs": 0,
        "counts_changed": False,
        "actual_run_adapter_hashes_changed": False,
    }
    (HERE / "exact_algorithms_branch_completion_fix.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
