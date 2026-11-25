#!/usr/bin/env python3
"""Pin a source-only patch and every C/header byte against frozen build eight."""

import difflib
import hashlib
import json
from pathlib import Path
from typing import Any

R = Path(__file__).resolve().parent
M = json.loads((R / "source.json").read_text())
S = Path(M["source_directory"])
B = Path(
    json.loads((R.parent / "exact_msolve_byte_exponent_tools/source.json").read_text())[
        "source_directory"
    ]
)


def sha(x):
    return hashlib.sha256(x).hexdigest()


files = sorted(
    {
        str(p.relative_to(t))
        for t in [B, S]
        for p in (t / "src").rglob("*")
        if p.is_file() and p.suffix in [".c", ".h"] and p.name != "msolve-version.h"
    }
)
patch = []
entries: list[dict[str, Any]] = []
for relative in files:
    old = (B / relative).read_bytes() if (B / relative).exists() else b""
    new = (S / relative).read_bytes() if (S / relative).exists() else b""
    entries.append(
        {
            "path": relative,
            "baseline_sha256": sha(old),
            "candidate_sha256": sha(new),
            "changed": old != new,
        }
    )
    if old != new:
        patch.extend(
            difflib.unified_diff(
                old.decode().splitlines(keepends=True),
                new.decode().splitlines(keepends=True),
                fromfile="a/" + relative if old else "/dev/null",
                tofile="b/" + relative,
            )
        )
data = "".join(patch).encode()
(R / "typed-byte-vectors.patch").write_bytes(data)
assert all(not e["changed"] for e in entries if Path(e["path"]).name.startswith("la_"))
for f in [
    "validation.json",
    "table_check.json",
    "guard_check.json",
    "compile_api_check.json",
]:
    assert json.loads((R / f).read_text())["status"] == "PASS", f
M.update(
    status="OWNER_VALIDATED_AWAITING_INDEPENDENT_REVIEW",
    executable_sha256=sha((R / "msolve").read_bytes()),
    patch=str(R / "typed-byte-vectors.patch"),
    patch_sha256=sha(data),
    source_files=entries,
    source_tree_sha256=sha(
        "".join(
            e["path"] + " " + e["candidate_sha256"] + "\n" for e in entries
        ).encode()
    ),
    successful_compile=json.loads(
        max(
            R.glob("compile_pass*.json"),
            key=lambda p: int(p.stem.removeprefix("compile_pass")),
        ).read_text()
    ),
    owner_reports=[
        "validation.json",
        "table_check.json",
        "guard_check.json",
        "compile_api_check.json",
    ],
    preserved_earlier_candidates=["candidate1", "candidate2"],
    full_board_solver_runs=0,
)
(R / "source.json").write_text(json.dumps(M, indent=2) + "\n")
print(
    json.dumps(
        {
            k: M[k]
            for k in [
                "status",
                "executable_sha256",
                "patch_sha256",
                "source_tree_sha256",
            ]
        },
        indent=2,
    )
)
print("changed source files:", sum(e["changed"] for e in entries), "of", len(entries))
