#!/usr/bin/env python3
"""Pin a source-only nibble-storage plan; does not patch, build, or run msolve."""

import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUILD = HERE / "exact_msolve_byte_exponent_tools"
SOURCE = BUILD / "msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2"


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    assert (
        sha(BUILD / "msolve")
        == "63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76"
    )
    selected = {
        "src/neogb/data.h": "logical exponent type and table layout",
        "src/neogb/hash.c": "all persistent storage, hash, divisor, LCM and promotion paths",
        "src/neogb/io.c": "dense input import and generic export",
        "src/neogb/order.c": "active DRL comparators; also compiled excluded orders",
        "src/neogb/symbol.c": "pair/reducer multiplier construction and symbolic insertion",
        "src/neogb/convert.c": "column conversion and ordinary/final promotion",
        "src/neogb/f4.c": "ordinary and final-interreduction control flow",
        "src/neogb/modular.c": "initial prime trace-wrapper setup; trace computations excluded",
        "src/neogb/engine.c": "scope guards and dispatch",
        "src/msolve/msolve.c": "prime export early return and leading-ideal extraction call",
        "src/msolve/iofiles.c": "active g1/g2 exponent output",
        "src/msolve/hilbert.c": "active get_lm_from_bs; staircase paths excluded",
        "src/msolve/linear.c": "compiled direct accesses, but extraction is after export-only return",
        "src/msolve/lifting-gb.c": "compiled QQ/trace outputs; excluded by prime/no-trace scope",
    }
    inventory = []
    for relative, note in selected.items():
        path = SOURCE / relative
        lines = path.read_text().splitlines()
        matches = [
            {"line": i + 1, "text": line.strip()}
            for i, line in enumerate(lines)
            if re.search(r"->ev\[|\bexp_t\b|\bevl\b|sizeof\(exp_t\)", line)
        ]
        inventory.append(
            {
                "file": relative,
                "sha256": sha(path),
                "scope_note": note,
                "matching_lines": matches,
            }
        )
    calculations = []
    for n in [93, 94, 95, 96, 97, 127]:
        dense = n + 1
        packed = 1 + (n + 1) // 2
        calculations.append(
            {
                "variables": n,
                "logical_lanes": dense,
                "byte_storage_bytes": dense,
                "packed_storage_bytes": packed,
                "per_vector_saving_bytes": dense - packed,
            }
        )
    logs = []
    for stem in [
        "exact_msolve_full_native3_minfill_byte_4g",
        "exact_msolve_full_native3_sign_minfill_byte_4g",
    ]:
        path = HERE / (stem + ".log")
        result = HERE / (stem + ".json")
        if not path.exists() or not result.exists():
            continue
        data = json.loads(result.read_text())
        n = data["variables"]
        matches = re.findall(
            r"MSOLVE_SYMBOLIC_CAPACITY_REQUEST[^\n]*exponent_new=(\d+)[^\n]*buckets_new=(\d+)",
            path.read_text(),
        )
        if not matches:
            continue
        capacity, buckets = map(int, matches[-1])
        dense = n + 1
        packed = 1 + (n + 1) // 2
        logs.append(
            {
                "log_file": path.name,
                "log_sha256": sha(path),
                "result_file": result.name,
                "result_status": data["status"],
                "variables": n,
                "last_logged_capacity_request": capacity,
                "last_logged_bucket_request": buckets,
                "request_success_not_attested": True,
                "hypothetical_same_capacity_exponent_saving_bytes": capacity
                * (dense - packed),
                "hypothetical_same_capacity_exponent_saving_mib": capacity
                * (dense - packed)
                / 1024**2,
                "observed_packed_memory_saving": False,
            }
        )
    report = {
        "status": "PLAN_ONLY_NO_BUILD",
        "scope": "representation feasibility and source-site inventory",
        "baseline_executable_sha256": sha(BUILD / "msolve"),
        "baseline_patch_sha256": sha(BUILD / "checked-byte-exponents.patch"),
        "source_commit": "cc044551f8e202d00691990fd3fd0b1226a88ea2",
        "algorithm_or_solver_source_changes": False,
        "builds": 0,
        "solver_runs": 0,
        "packing_bound": "stored coordinate<=15 checked before packing; degree<=255 checked; no universal coordinate15 theorem",
        "storage_calculations": calculations,
        "terminal_log_calculations": logs,
        "inventory_is_static_not_complete_reachability_proof": True,
        "source_inventory": inventory,
        "inventory_generator_sha256": sha(Path(__file__)),
    }
    (HERE / "exact_msolve_nibble_plan.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(
        json.dumps(
            {
                k: report[k]
                for k in [
                    "status",
                    "builds",
                    "solver_runs",
                    "storage_calculations",
                    "terminal_log_calculations",
                ]
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
