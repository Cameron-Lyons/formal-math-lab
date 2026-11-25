#!/usr/bin/env python3
"""Check/regenerate a finite certificate excluding non-global fixed cellwise gauges.

Only the standard library is used. Verification audits the explicit boards,
XOR identities, full one-hot rank, anchor argument geometry, and spatial factor
symmetries. No enumeration of all valid ternary boards is assumed.
"""

import argparse
import hashlib
import json
from collections import Counter
from itertools import permutations
from math import factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT = ROOT / "experiments/exact_structure_gauge_certificate.json"


def geometry():
    coordinates = [(j - r, -r) for r in range(10) for j in range(2 * r + 1)]
    index = {xy: i for i, xy in enumerate(coordinates)}
    windows = []
    for x, y in coordinates:
        points = [(x, y + 1), (x - 1, y), (x, y), (x + 1, y)]
        if all(p in index for p in points):
            windows.append(tuple(index[p] for p in points))
    assert len(windows) == 81
    roles = {role: sorted({w[a] for w in windows}) for a, role in enumerate("TLMR")}
    assert all(len(s) == 81 for s in roles.values())
    return windows, roles


def reflected(flat):
    return "".join(flat[r * r : (r + 1) ** 2][::-1] for r in range(10))


def compressed(flat, positions):
    value = 1
    for i, pos in enumerate(positions):
        color = int(flat[pos])
        if color < 2:
            value |= 1 << (1 + 2 * i + color)
    return value


def full_one_hot(flat, positions):
    return 1 | sum(1 << (1 + 3 * i + int(flat[pos])) for i, pos in enumerate(positions))


def rank(vectors):
    basis = {}
    for vector in vectors:
        while vector:
            pivot = vector.bit_length() - 1
            if pivot in basis:
                vector ^= basis[pivot]
            else:
                basis[pivot] = vector
                break
    return len(basis)


def test_set(data):
    boards = {record["flat"] for record in data["boards"]}
    boards |= {reflected(record["flat"]) for record in data["boards"]}
    boards |= {
        "".join(str((int(c) + shift) % 3) for c in data["anchor"]) for shift in range(3)
    }
    return boards


def candidates():
    palettes = [str.maketrans("012", "".join(p)) for p in permutations("012")]
    for item in json.loads((ROOT / "extended_seeds.json").read_text()):
        flat = "".join(item["rows"])
        for pi, palette in enumerate(palettes):
            yield flat.translate(palette), ["extended_seeds.json", item["index"], pi]
    for name in [
        "splice_witnesses.json",
        "splice_extension.json",
        "splice_further.json",
        "splice_next.json",
    ]:
        for gi, group in enumerate(json.loads((ROOT / name).read_text())["groups"]):
            for ci, cap in enumerate(group["caps"]):
                for ti, tail in enumerate(group.get("tails", [])[:4]):
                    flat = cap + group["pivot"] + tail
                    for pi, palette in enumerate(palettes):
                        yield flat.translate(palette), [name, gi, ci, ti, pi]


def generate():
    _, roles = geometry()
    positions = roles["L"]
    basis, selected = {}, []
    for flat, source in candidates():
        vector = compressed(flat, positions)
        combination = 1 << len(selected)
        while vector:
            pivot = vector.bit_length() - 1
            if pivot in basis:
                v, c = basis[pivot]
                vector ^= v
                combination ^= c
            else:
                basis[pivot] = (vector, combination)
                selected.append({"flat": flat, "source": source})
                break
        if len(selected) == 161:
            break
    assert len(selected) == 161
    relations = []
    for i, pos in enumerate(positions[1:], start=1):
        for color in range(2):
            vector = (1 << (1 + color)) ^ (1 << (1 + 2 * i + color))
            combination = 0
            while vector:
                pivot = vector.bit_length() - 1
                v, c = basis[pivot]
                vector ^= v
                combination ^= c
            assert combination.bit_count() % 2 == 0
            relations.append(
                {"cell": pos, "color": color, "xor_boards": hex(combination)}
            )
    anchor = "".join(
        json.loads((ROOT / "sources/anc/certificates.json").read_text())[
            "ternary_seeds"
        ][0]
    )
    data = {
        "format": "ternary-fixed-cellwise-gauge-certificate-v1",
        "scope": "Fixed independent cellwise color permutations; no cell relocation or board-dependent choices.",
        "role": "L",
        "positions": positions,
        "reference_cell": positions[0],
        "lifted_full_columns": 244,
        "rank_over_F2": 161,
        "boards": selected,
        "xor_relations": relations,
        "anchor": anchor,
        "finite_test_set_size": 0,
        "claim": "Any fixed cellwise palette permutation taking every generated test board to a valid board is global.",
    }
    data["finite_test_set_size"] = len(test_set(data))
    return data


def check_spatial(windows):
    sets = list(map(frozenset, windows))
    neighbors = [
        {j for j in range(81) if j != i and len(sets[i] & sets[j]) == 2}
        for i in range(81)
    ]
    unseen = set(range(81))
    paths: list[list[int]] = []
    while unseen:
        root = min(unseen)
        component = {root}
        pending = [root]
        while pending:
            v = pending.pop()
            for w in neighbors[v] - component:
                component.add(w)
                pending.append(w)
        unseen -= component
        if len(component) == 1:
            path = [root]
        else:
            ends = [v for v in component if len(neighbors[v]) == 1]
            assert len(ends) == 2 and all(
                len(neighbors[v]) in (1, 2) for v in component
            )
            path = [min(ends)]
            previous = None
            while True:
                options = neighbors[path[-1]] - (
                    {previous} if previous is not None else set()
                )
                if not options:
                    break
                assert len(options) == 1
                previous = path[-1]
                path.append(next(iter(options)))
            assert set(path) == component
        paths.append(path)
    paths.sort(key=len)
    assert list(map(len, paths)) == list(range(1, 18, 2))
    incidences = [
        sum(1 << i for i, w in enumerate(windows) if cell in w) for cell in range(100)
    ]
    assert len(set(incidences)) == 100
    lookup = {bits: cell for cell, bits in enumerate(incidences)}
    maps = []
    for orientation in range(256):
        wp = list(range(81))
        for i, path in enumerate(paths[1:]):
            if orientation >> i & 1:
                for old, new in zip(path, reversed(path), strict=False):
                    wp[old] = new
        image = []
        for bits in incidences:
            mapped = 0
            while bits:
                bit = bits & -bits
                bits ^= bit
                mapped |= 1 << wp[bit.bit_length() - 1]
            if mapped not in lookup:
                break
            image.append(lookup[mapped])
        else:
            assert len(set(image)) == 100
            assert {frozenset(image[c] for c in w) for w in windows} == set(sets)
            maps.append(tuple(image))
    mirror = tuple(r * r + 2 * r - j for r in range(10) for j in range(2 * r + 1))
    assert set(maps) == {tuple(range(100)), mirror}
    return len(maps)


def matching_count(flat):
    starts = [3 * int(flat[r * r]) + int(flat[r * r + 1]) for r in range(1, 10)]
    ends = [
        3 * int(flat[(r + 1) ** 2 - 2]) + int(flat[(r + 1) ** 2 - 1])
        for r in range(1, 10)
    ]
    d = Counter(starts)
    expected = 1
    for count in d.values():
        expected *= factorial(count)
    if d != Counter(ends):
        expected = 0
    dp = [0] * 512
    dp[0] = 1
    for mask in range(511):
        row = mask.bit_count()
        for col in range(9):
            if not mask >> col & 1 and ends[row] == starts[col]:
                dp[mask | (1 << col)] += dp[mask]
    assert dp[-1] == expected
    return {
        "start_pair_counts": dict(sorted(d.items())),
        "compatible_matchings": dp[-1],
    }


def check(path):
    data = json.loads(path.read_text())
    windows, roles = geometry()
    assert data["format"] == "ternary-fixed-cellwise-gauge-certificate-v1"
    positions = data["positions"]
    assert positions == roles["L"]
    selected = [record["flat"] for record in data["boards"]]
    assert len(selected) == len(set(selected)) == 161
    tests = test_set(data)
    assert len(tests) == data["finite_test_set_size"] == 322
    for flat in tests:
        assert len(flat) == 100 and set(flat) <= set("012")
        patterns = [tuple(int(flat[c]) for c in w) for w in windows]
        assert len(set(patterns)) == 81
    vectors = [compressed(flat, positions) for flat in selected]
    relations = data["xor_relations"]
    assert len(relations) == 160
    expected = {(pos, c) for pos in positions[1:] for c in range(2)}
    assert {(r["cell"], r["color"]) for r in relations} == expected
    for relation in relations:
        mask = int(relation["xor_boards"], 16)
        assert mask.bit_length() <= 161 and mask.bit_count() % 2 == 0
        value = 0
        while mask:
            bit = mask & -mask
            mask ^= bit
            value ^= vectors[bit.bit_length() - 1]
        i = positions.index(relation["cell"])
        c = relation["color"]
        assert value == (1 << (1 + c)) ^ (1 << (1 + 2 * i + c))
    full = [full_one_hot(flat, positions) for flat in selected]
    local = [1 | (7 << (1 + 3 * i)) for i in range(81)]
    global_color = [1 | sum(1 << (1 + 3 * i + c) for i in range(81)) for c in range(3)]
    assert rank(full) == rank(vectors) == 161
    assert rank(local + global_color) == 83
    assert all((v & r).bit_count() % 2 == 0 for v in full for r in local + global_color)
    assert set(range(100)) - (set(roles["L"]) | set(roles["R"])) == {0, 2}
    assert len(set(roles["L"]) & set(roles["R"])) == 64
    assert data["anchor"][0] == data["anchor"][2] == "0"
    pairs = {
        a + b: len(set(roles[a]) & set(roles[b]))
        for i, a in enumerate("TLMR")
        for b in "TLMR"[i + 1 :]
    }
    assert pairs == {"TL": 64, "TM": 64, "TR": 64, "LM": 72, "LR": 64, "MR": 72}
    result = {
        "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "valid_test_boards": len(tests),
        "selected_boards": len(selected),
        "explicit_xor_identities": len(relations),
        "full_lifted_columns": 244,
        "rank_over_F2": rank(full),
        "dual_relation_rank": rank(local + global_color),
        "exceptional_cells": [0, 2],
        "role_intersections": pairs,
        "spatial_incidence_automorphisms": check_spatial(windows),
        "anchor_endpoint_matching": matching_count(data["anchor"]),
        "result": "PASS",
        "full_count_computed": False,
    }
    print(json.dumps(result, indent=2))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=DEFAULT)
    parser.add_argument(
        "--regenerate",
        type=Path,
        help="Write regenerated data to this path, then check it.",
    )
    parser.add_argument("--output", type=Path, help="Save the audit JSON.")
    args = parser.parse_args()
    path = args.certificate
    if args.regenerate:
        path = args.regenerate
        path.write_text(json.dumps(generate(), indent=2) + "\n")
    result = check(path)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
