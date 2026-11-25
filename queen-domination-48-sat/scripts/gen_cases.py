#!/usr/bin/env python3
# Modified from lean/scripts/gen_cases.py of https://github.com/jasondavies/queen-domination (Apache-2.0):
# the arguments LABEL and WHOSE, the module prefix, and the wording of the header.
"""Generate the Lean files of the case list of a frame-method run from the referee's run logs
(read-only input):

  DIR/Cases<N>Data.lean         the case codes, one `def` per pair of horizontal margins (ml, mr), and
                                the table `caseCodes<N>T` with `caseCodes<N>T[ml][mr]` = that def;
  DIR/Cases<N>Pieces.lean       one kernel computation (`decide +kernel`) per pair (ml, mr) with
                                ml + mr <= k:  casesPQ N K ml mr = (tableCodes caseCodes<N>T ml mr).map Case.ofCode,
                                and the assembled equation  enumCases N K = (tableList K caseCodes<N>T).map Case.ofCode.

usage: python3 -B scripts/gen_cases.py N K /path/to/frame/out DIR [LABEL [WHOSE]]
       DIR: the directory of the Lean files; its name is the module prefix (here Queens48);
       LABEL: how the header names the directory of the run logs (default: frame/out);
       WHOSE: whose run the header says it is (default: "the referee's"; n = 48: "the")

The list consists of the cases refuted by the run (scripts/runlog.py: plain records UNSAT + VERIFIED, or a
cover by verified cube records).  Each case (ml, mr, mb, mt, dR, dC, dT, dS) is one decimal numeral
ml mr mb mt (two digits each) dR dC dT dS (one digit each); each def is sorted."""

import os
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from runlog import analyse, code  # noqa: E402

n, k, outdir, leandir = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
label = sys.argv[5].rstrip("/") if len(sys.argv) > 5 else "frame/out"
whose = sys.argv[6] if len(sys.argv) > 6 else "the referee's"
refuted, info, keys = analyse(outdir, n, k)
assert info["sat_records"] == 0 and info["n_keys_not_refuted"] == 0, info
pairs = [(p, q) for p in range(k + 1) for q in range(k + 1 - p)]  # = marginPairs k
by_pq = {}
for c in refuted:
    assert c[:2] in set(pairs), c
    by_pq.setdefault(c[:2], []).append(code(c))
for v in by_pq.values():
    assert v == sorted(v)

hdr = [
    "/-",
    "GENERATED FILE -- do not edit.  Produced by scripts/gen_cases.py from the run logs",
]
for fn, d in info["files"].items():
    if d["sha256"]:
        uncomp = " of the uncompressed text" if fn.endswith(".xz") else ""
        hdr.append(
            f"  {label}/{fn:<20} ({d['records']:6d} records, sha256{uncomp} {d['sha256']})"
        )
nframes = len({c[:4] for c in refuted})
hdr.append(
    f"of {whose} frame-method run for n = {n:d}, k = {k:d}: {len(refuted):d} cases, {nframes:d} frames;"
)
hdr.append(
    f"{info['plain_refuted']:d} refuted by a plain record (UNSAT, drat-trim VERIFIED), "
    f"{info['cube_refuted']:d} by verified cube records of run_hard.py."
)

data = [
    *hdr,
    "Each numeral encodes one case (ml, mr, mb, mt, dR, dC, dT, dS) in decimal as",
    "  ml mr mb mt (two digits each) dR dC dT dS (one digit each);",
    f"`caseCodes{n:d}T[ml][mr]` lists the cases with horizontal margins (ml, mr), sorted.",
    "`QueenDom.Case.ofCode` decodes a numeral.",
    "-/",
    "",
    "module",
    "",
    "@[expose] public section",
    "",
    "namespace QueenDom",
    "",
]
for p, q in pairs:
    if (p, q) not in by_pq:
        continue
    ch = by_pq[(p, q)]
    data.append("set_option maxRecDepth 100000 in")
    data.append(
        f"/-- The {len(ch):d} cases with (ml, mr) = ({p:d}, {q:d}) of the n = {n:d}, k = {k:d} run. -/"
    )
    data.append(f"def caseCodes{n:d}_{p:d}_{q:d} : List Nat := [")
    data.extend(
        "  "
        + ", ".join(str(c) for c in ch[i : i + 8])
        + ("," if i + 8 < len(ch) else "")
        for i in range(0, len(ch), 8)
    )
    data.append("]")
    data.append("")
data.append(
    f"/-- The table of the case codes of the n = {n:d}, k = {k:d} run: row `ml`, column `mr`. -/"
)
data.append(f"def caseCodes{n:d}T : List (List (List Nat)) := [")
for p in range(k + 1):
    row = [
        f"caseCodes{n:d}_{p:d}_{q:d}" if (p, q) in by_pq else "[]"
        for q in range(k + 1 - p)
    ]
    data.append("  [" + ", ".join(row) + "]" + ("," if p < k else ""))
data.append("]")
data += ["", "end QueenDom", ""]

pc = [
    *hdr,
    f"Kernel computations: the case list `L({n:d}, {k:d})` is the decoded table `caseCodes{n:d}T`, checked piece",
    "by piece (one theorem per pair of horizontal margins (ml, mr), so that each kernel computation is",
    "small and the pieces are checked in parallel).  No `native_decide`.",
    "-/",
    "",
    "module",
    "",
    "public import QueenDom.Main",
    f"public import {os.path.basename(os.path.abspath(leandir))}.Cases{n:d}Data",
    "",
    "@[expose] public section",
    "",
    "namespace QueenDom",
    "",
    "set_option maxRecDepth 100000 in",
    f"/-- The {len(pairs):d} pairs `(ml, mr)` with `ml + mr <= {k:d}`. -/",
    f"theorem marginPairs_{k:d} : marginPairs {k:d} = [",
]
pc.extend(
    "    "
    + ", ".join(f"({p:d}, {q:d})" for p, q in pairs[i : i + 12])
    + ("," if i + 12 < len(pairs) else "")
    for i in range(0, len(pairs), 12)
)
pc += ["  ] := by decide +kernel", ""]
for p, q in pairs:
    pc.append("set_option maxRecDepth 100000 in")
    pc.append("set_option maxHeartbeats 0 in")
    pc.append(
        f"theorem piece{n:d}_{p:d}_{q:d} : casesPQ {n:d} {k:d} {p:d} {q:d} = (tableCodes caseCodes{n:d}T {p:d} {q:d}).map Case.ofCode := by"
    )
    pc.append("  decide +kernel")
    pc.append("")
term = "List.forall_mem_nil _"
for p, q in reversed(pairs):
    term = f"List.forall_mem_cons.2 ⟨piece{n:d}_{p:d}_{q:d},\n    {term}⟩"
pc += [
    "set_option maxRecDepth 100000 in",
    f"/-- **The case list `L({n:d}, {k:d})` is the decoded table of the run** (assembled from the pieces). -/",
    f"theorem enumCases_{n:d}_{k:d}_table : enumCases {n:d} {k:d} = (tableList {k:d} caseCodes{n:d}T).map Case.ofCode := by",
    "  refine enumCases_eq_table ?_",
    f"  rw [marginPairs_{k:d}]",
    "  exact " + term,
    "",
    "end QueenDom",
    "",
]
with open(os.path.join(leandir, f"Cases{n:d}Data.lean"), "w") as f:
    f.write("\n".join(data))
with open(os.path.join(leandir, f"Cases{n:d}Pieces.lean"), "w") as f:
    f.write("\n".join(pc))
print(
    f"n={n:d} k={k:d}: {len(refuted):d} cases, {nframes:d} frames, "
    f"{len(by_pq):d} nonempty pieces of {len(pairs):d}; "
    f"written Cases{n:d}Data.lean, Cases{n:d}Pieces.lean"
)
