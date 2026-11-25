#!/usr/bin/env python3
"""Exact polynomial by placement-partition Möbius inversion, small heights only."""

import argparse
import json
import time
from collections import Counter, defaultdict
from math import factorial
from pathlib import Path


def windows(height):
    return [
        ((r - 1) ** 2 + j, r * r + j, r * r + j + 1, r * r + j + 2)
        for r in range(1, height)
        for j in range(2 * r - 1)
    ]


def partitions(n):
    blocks = []

    def visit(i):
        if i == n:
            yield tuple(tuple(block) for block in blocks)
            return
        for block in blocks:
            block.append(i)
            yield from visit(i + 1)
            block.pop()
        blocks.append([i])
        yield from visit(i + 1)
        blocks.pop()

    yield from visit(0)


def cell_partition(height, blocks):
    w = windows(height)
    parents = list(range(height * height))

    def find(a):
        while parents[a] != a:
            parents[a] = parents[parents[a]]
            a = parents[a]
        return a

    for block in blocks:
        if len(block) < 2:
            continue
        first = w[block[0]]
        for i in block[1:]:
            for a, b in zip(first, w[i], strict=False):
                a = find(a)
                b = find(b)
                if a != b:
                    parents[b] = a
    relabel = {}
    result = []
    for i in range(height * height):
        root = find(i)
        if root not in relabel:
            relabel[root] = len(relabel)
        result.append(relabel[root])
    return bytes(result)


def placement_closure(height, cells):
    classes = {}
    result = []
    for w in windows(height):
        signature = tuple(cells[p] for p in w)
        if signature not in classes:
            classes[signature] = len(classes)
        result.append(classes[signature])
    return bytes(result)


def evaluate(coefficients, q):
    return sum(v * q ** int(k) for k, v in coefficients.items())


def compute(height):
    if not 1 <= height <= 4:
        raise ValueError("Direct partition enumeration is bounded to heights 1..4.")
    started = time.monotonic()
    weighted = Counter()
    fibers = Counter()
    poly = Counter()
    count = 0
    for blocks in partitions((height - 1) ** 2):
        mu = 1
        for block in blocks:
            mu *= (-1) ** (len(block) - 1) * factorial(len(block) - 1)
        key = cell_partition(height, blocks)
        weighted[key] += mu
        fibers[key] += 1
        poly[max(key) + 1] += mu
        count += 1
    coefficients = {k: v for k, v in sorted(poly.items(), reverse=True) if v}
    closures = {placement_closure(height, key): key for key in weighted}
    assert len(closures) == len(weighted)
    for closure, cells in closures.items():
        grouped = defaultdict(list)
        for i, label in enumerate(closure):
            grouped[label].append(i)
        assert cell_partition(height, list(grouped.values())) == cells
    return (
        {
            "height": height,
            "cells": height * height,
            "placements": (height - 1) ** 2,
            "placement_partitions": count,
            "cell_closures": len(weighted),
            "nonzero_mobius_closures": sum(v != 0 for v in weighted.values()),
            "largest_closure_fiber": max(fibers.values()),
            "coefficients": coefficients,
            "evaluations": {q: evaluate(coefficients, q) for q in range(1, 6)},
            "fiber_size_histogram": dict(sorted(Counter(fibers.values()).items())),
            "seconds": time.monotonic() - started,
        },
        weighted,
        closures,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--height", type=int, choices=range(1, 5))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    results = []
    for height in [args.height] if args.height else range(1, 5):
        data, _, _ = compute(height)
        results.append(data)
        print(json.dumps(data), flush=True)
    if args.output:
        args.output.write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
