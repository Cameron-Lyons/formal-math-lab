#!/usr/bin/env python3
"""Read-only search for usable retained polynomials in incomplete msolve runs."""

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
INDEX = HERE / "exact_msolve_current_trials_audit.json"
OUTPUT = HERE / "exact_polynomial_upper_failed_artifacts_extended.json"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if OUTPUT.exists():
        raise FileExistsError(OUTPUT)
    index = json.loads(INDEX.read_text())
    names = {entry["name"] for entry in index["trials"]}
    for path in HERE.glob("exact_msolve_full*.json"):
        data = json.loads(path.read_text())
        if data.get("status") in (
            "BACKEND_ERROR",
            "INCOMPLETE_TIMEOUT",
            "POSTPROCESS_ERROR",
        ):
            names.add(path.stem)
    records = []
    for name in sorted(names):
        data_path = HERE / (name + ".json")
        data = json.loads(data_path.read_text())
        basis, leading, log = [
            HERE / (name + suffix) for suffix in (".basis", ".leading.json", ".log")
        ]
        text = log.read_text(errors="replace")
        record = {
            "name": name,
            "status": data["status"],
            "basis_bytes": basis.stat().st_size,
            "leading_export_exists": leading.exists(),
            "completion_markers": sum(
                line.strip() == "MSOLVE_PRIME_GB_EXPORT_COMPLETE"
                for line in text.splitlines()
            ),
            "metadata_sha256": digest(data_path),
            "basis_sha256": digest(basis),
            "log_sha256": digest(log),
        }
        assert record["basis_bytes"] == record["completion_markers"] == 0
        assert not record["leading_export_exists"]
        records.append(record)
    result = {
        "status": "CHECKED_NO_RETAINED_INTERMEDIATE_POLYNOMIALS",
        "scope": "consolidated trials plus all terminal exact_msolve_full metadata",
        "trial_count": len(records),
        "trials": records,
        "exact_board_count": None,
        "new_upper_bound_from_failed_runs": None,
        "matrix_dimensions_are_not_polynomial_certificates": True,
        "audit_sha256": digest(Path(__file__)),
        "index_sha256": digest(INDEX),
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"], len(records))


if __name__ == "__main__":
    main()
