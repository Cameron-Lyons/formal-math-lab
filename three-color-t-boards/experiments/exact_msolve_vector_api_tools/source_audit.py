#!/usr/bin/env python3
"""Lexical boundary inventory and exact source comparison; complements review."""

import importlib.util
import json
import re
from pathlib import Path
from typing import Any

R = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "accessor_conversion", R / "accessor_conversion.py"
)
assert spec is not None and spec.loader is not None
accessor_conversion = importlib.util.module_from_spec(spec)
spec.loader.exec_module(accessor_conversion)
S = accessor_conversion.S
mask = accessor_conversion.mask
functions = accessor_conversion.functions
B = Path(
    json.loads((R.parent / "exact_msolve_byte_exponent_tools/source.json").read_text())[
        "source_directory"
    ]
)
files: list[dict[str, Any]] = []
failures = []
for p in (S / "src").rglob("*"):
    if p.suffix not in [".c", ".h"]:
        continue
    text = p.read_text()
    m = mask(text)
    relative = str(p.relative_to(S))
    if p.name == "stored_exp.h":
        continue
    if accessor_conversion.direct(text)[1]:
        failures.append([relative, "direct scalar table indexing"])
    if re.search(r"\b\w+\.byte\b|\b\w+->byte\b", m):
        failures.append([relative, "representation field outside API"])
    reads = writes = copies = 0
    for a, _b, c in functions(text):
        f = m[a:c]
        names = {
            q[1] for q in re.finditer(r"\bstored_exp_t\s*\*\s*(?:const\s+)?(\w+)\b", f)
        }
        failures.extend(
            [relative, "raw stored scalar alias " + name]
            for name in names
            if re.search(r"(?<![A-Za-z0-9_>.])" + name + r"\s*\[", f)
        )
        for q in re.finditer(r"\bmem(?:cpy|move|set)\s*\(", f):
            end = accessor_conversion.close(f, f.find("(", q.start()), "(", ")")
            args = f[q.start() : end]
            if re.search(r"->ev\b", args) or any(
                re.search(r"\b" + name + r"\b", args) for name in names
            ):
                failures.append(
                    [
                        relative,
                        "raw memory boundary",
                        text[: a + q.start()].count("\n") + 1,
                        args,
                    ]
                )
    reads = len(re.findall(r"\bstored_exp_read\(", m))
    writes = len(re.findall(r"\bstored_exp_write\(", m))
    copies = len(re.findall(r"\bstored_exp_(?:copy|copy_vectors|import|export)\(", m))
    if reads + writes + copies:
        files.append(
            {"path": relative, "reads": reads, "writes": writes, "copies": copies}
        )
assert not failures, failures
unchanged = []
for p in (S / "src").rglob("*"):
    if p.is_file() and (
        p.name.startswith("la_")
        or p.name in ["byte_input_guard.h", "byte_model_guard.h"]
    ):
        assert p.read_bytes() == (B / p.relative_to(S)).read_bytes(), p
        unchanged.append(str(p.relative_to(S)))
record = {
    "status": "PASS",
    "scope": "lexical inventory, not a substitute for independent semantic review",
    "raw_stored_scalar_or_memory_bypasses": 0,
    "files": files,
    "unchanged_coefficient_and_guard_files": unchanged,
    "manual_physical_storage_audit": {
        "file": "src/neogb/hash.c",
        "constructors": [
            "initialize_basis_hash_table",
            "copy_hash_table",
            "initialize_secondary_hash_table",
        ],
        "all_stored_strides": "evbytes",
        "all_dense_arithmetic_bounds": "evl",
        "growth_and_lifetimes": [
            "enlarge_hash_table",
            "reinitialize_hash_table",
            "reserve_hash_table_checked",
            "stage_missing_symbolic_exponents",
            "reset_hash_table",
        ],
        "slot_zero": "dense stack import; excluded scratch uses checked stored writes",
        "final_export": [
            "src/neogb/f4.c:reduce_basis",
            "src/msolve/hilbert.c:get_lm_from_bs",
            "src/msolve/iofiles.c:print_ff_basis_data",
        ],
    },
    "ordinary_reset_reachable": False,
}
(R / "source_audit.json").write_text(json.dumps(record, indent=2) + "\n")
print(
    "PASS: no raw stored scalar/memory bypass; coefficient kernels and scope guards unchanged"
)
print(
    "read/write/copy sites",
    *[sum(f[k] for f in files) for k in ["reads", "writes", "copies"]],
)
