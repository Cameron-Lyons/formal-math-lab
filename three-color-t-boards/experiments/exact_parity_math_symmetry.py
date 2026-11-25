#!/usr/bin/env python3
"""Finite audit of cap orbits; no fixed-prefix extension counts are computed."""

import json
from itertools import permutations, product
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
EXPECTED = {
    "0000": 3,
    "0001": 12,
    "0010": 6,
    "0011": 12,
    "0012": 12,
    "0101": 6,
    "0102": 6,
    "0111": 6,
    "0112": 12,
    "0121": 6,
}


def action(cap, palette, reflection):
    order = (0, 3, 2, 1) if reflection else (0, 1, 2, 3)
    return "".join(str(palette[int(cap[i])]) for i in order)


def main():
    group = list(product(permutations(range(3)), (False, True)))
    subgroup = [g for g in group if g[0][0] == 0]
    caps = ["".join(map(str, c)) for c in product(range(3), repeat=4)]
    fibers = {}
    for cap in caps:
        orbit = {action(cap, *g) for g in group}
        representative = min(orbit)
        fibers.setdefault(representative, set()).add(cap)
        assert len(orbit) == EXPECTED[representative]
    assert {rep: len(orbit) for rep, orbit in fibers.items()} == EXPECTED
    assert sum(map(len, fibers.values())) == 81
    rows: list[dict[str, Any]] = []
    for representative, orbit in sorted(fibers.items()):
        stabilizer = [g for g in group if action(representative, *g) == representative]
        residual_orbit = {action(representative, *g) for g in subgroup}
        assert residual_orbit == {cap for cap in orbit if cap[0] == "0"}
        assert len(stabilizer) * len(orbit) == 12
        assert len(residual_orbit) * 3 == len(orbit)
        rows.append(
            {
                "representative": representative,
                "full_orbit_size": len(orbit),
                "apex_zero_orbit_size": len(residual_orbit),
                "stabilizer_order": len(stabilizer),
                "stabilizer": [
                    {"palette": list(p), "reflection": r} for p, r in stabilizer
                ],
            }
        )
    assert sum(row["apex_zero_orbit_size"] for row in rows) == 27
    report = {
        "status": "PASS",
        "scope": "cap-orbit partition only; extension counts unevaluated",
        "cap_order": "top,left,middle,right; row-major first two rows",
        "group_order": 12,
        "residual_group_order_at_apex_zero": 4,
        "total_caps": 81,
        "apex_zero_caps": 27,
        "orbits": rows,
        "completion_rule": "All10 raw fixed-prefix counts must be exact before weighted sum is an exact total; alternatively one exact apex0 count suffices after multiplying by3.",
    }
    (HERE / "exact_parity_math_symmetry_results.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
