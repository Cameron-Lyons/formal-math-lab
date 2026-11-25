#!/usr/bin/env python3
"""Small, self-contained checks of tagged-rotor noncommutativity.

Only two previously published boards are decoded; no board search or solver.
The default writes an audit JSON; --check verifies the existing audit exactly.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path


FIXTURES = {
    "binary_existing_structure_witness": [
        "0", "000", "00111", "1101011", "111001000",
    ],
    "ternary_published_seed_0": [
        "0", "000", "00100", "0020110", "012021022",
        "10110211112", "0121222022001", "122101020222001",
        "22211121210122112", "1201100021201000200",
    ],
}


def geometric_check(q, rows):
    assert len(rows) == q * q + 1
    assert all(len(row) == 2 * r + 1 for r, row in enumerate(rows))
    cells = {(j - r, -r): value for r, row in enumerate(rows)
             for j, value in enumerate(row)}
    assert all(0 <= value < q for value in cells.values())
    occurrences = Counter()
    for x, y in cells:
        positions = [(x, y + 1), (x - 1, y), (x, y), (x + 1, y)]
        if all(p in cells for p in positions):
            occurrences[tuple(cells[p] for p in positions)] += 1
    assert occurrences == Counter(product(range(q), repeat=4))


def slots(q):
    return [(r, j) for r in range(1, q * q + 1)
            for j in range(2 * r - 1)]


def boundary_cells(q):
    return [(0, 0)] + [(r, j) for r in range(1, q * q + 1)
                      for j in (0, 1)]


def legal_order(q, order):
    assert len(order) == q**4 and set(order) == set(slots(q))
    known = set(boundary_cells(q))
    for r, j in order:
        assert {(r - 1, j), (r, j), (r, j + 1)} <= known
        assert (r, j + 2) not in known
        known.add((r, j + 2))
    assert len(known) == (q * q + 1)**2


def encode(q, rows, order):
    legal_order(q, order)
    rotors = [[] for _ in range(q**3)]
    for r, j in order:
        g = q*q*rows[r - 1][j] + q*rows[r][j] + rows[r][j + 1]
        rotors[g].append(rows[r][j + 2])
    assert all(sorted(rotor) == list(range(q)) for rotor in rotors)
    boundary = [rows[r][j] for r, j in boundary_cells(q)]
    return boundary, rotors


def decode(q, boundary, rotors, order):
    legal_order(q, order)
    assert len(boundary) == 2*q*q + 1 and len(rotors) == q**3
    assert all(sorted(rotor) == list(range(q)) for rotor in rotors)
    values = dict(zip(boundary_cells(q), boundary))
    used, trace = [0] * (q**3), []
    for r, j in order:
        triple = [values[r - 1, j], values[r, j], values[r, j + 1]]
        g = q*q*triple[0] + q*triple[1] + triple[2]
        record = {"slot": [r, j], "input": triple, "prior_uses": used[g]}
        if used[g] == q:
            record["result"] = "CAPACITY_FAIL"
            trace.append(record)
            return {"status": "CAPACITY_FAIL", "completed_slots": len(trace) - 1,
                    "trace": trace, "usage": used}
        output = rotors[g][used[g]]
        values[r, j + 2] = output
        used[g] += 1
        record["output"] = output
        trace.append(record)
    rows = [[values[r, j] for j in range(2*r + 1)]
            for r in range(q*q + 1)]
    assert used == [q] * (q**3)
    geometric_check(q, rows)
    return {"status": "COMPLETE", "completed_slots": len(trace),
            "rows": rows, "usage": used}


def audit():
    cases = []
    for name, strings in FIXTURES.items():
        q = 2 if name.startswith("binary") else 3
        rows = [list(map(int, row)) for row in strings]
        geometric_check(q, rows)
        order = slots(q)
        swapped_order = [order[1], order[0]] + order[2:]
        legal_order(q, order)
        legal_order(q, swapped_order)
        boundary, rotors = encode(q, rows, order)
        normal = decode(q, boundary, rotors, order)
        assert normal["status"] == "COMPLETE" and normal["rows"] == rows
        swapped = decode(q, boundary, rotors, swapped_order)
        assert swapped["status"] == "CAPACITY_FAIL"
        assert swapped["completed_slots"] == (2 if q == 2 else 4)
        new_boundary, new_rotors = encode(q, rows, swapped_order)
        assert new_boundary == boundary
        expected_rotors = [rotor[:] for rotor in rotors]
        expected_rotors[0][0], expected_rotors[0][1] = (
            expected_rotors[0][1], expected_rotors[0][0])
        assert new_rotors == expected_rotors
        reencoded = decode(q, boundary, new_rotors, swapped_order)
        assert reencoded["status"] == "COMPLETE" and reencoded["rows"] == rows
        cases.append({
            "fixture": name, "q": q, "rows": strings,
            "boundary": boundary, "rotors_lexicographic_triples": rotors,
            "row_major_usage": normal["usage"],
            "row_major_completed_slots": normal["completed_slots"],
            "swapped_first_slots": [list(p) for p in swapped_order[:2]],
            "swapped_same_tuple_result": swapped,
            "reencoded_changed_rotor": {
                "triple": [0, 0, 0], "before": rotors[0], "after": new_rotors[0]},
            "reencoded_same_board": True,
        })
    return {"status": "PASS", "scope": "two existing fixtures; no search or total count",
            "coordinate_geometry_verified": True,
            "both_schedules_topological": True, "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    path = Path(__file__).with_suffix(".json")
    result = audit()
    if args.check:
        assert json.loads(path.read_text()) == result
    else:
        path.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: two valid fixtures; legal schedule swaps change acceptance; "
          "local rotor re-encoding restores each board. No count computed.")


if __name__ == "__main__":
    main()
