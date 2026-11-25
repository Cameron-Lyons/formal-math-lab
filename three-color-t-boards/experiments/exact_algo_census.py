#!/usr/bin/env python3
"""Exact census of distinct-pattern top caps, partitioned by prefix orbits.

This does not count full ternary boards. Symmetry is applied only to the
prescribed prefix; multiplicities are calculated by explicit enumeration,
so prefixes with stabilizers are handled correctly. Each suffix count is
exhaustive and the result is reported only after every partition completes.
"""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import subprocess
import time
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def normalize(word):
    table = {}
    return ''.join(str(table.setdefault(c, len(table))) for c in word)


def canonical(word, rows):
    reflected = ''.join(word[r*r:(r+1)**2][::-1] for r in range(rows))
    return min(normalize(word), normalize(reflected))


def independent_patterns(word, q, rows):
    # Coordinate-based window enumeration, separate from C++ index table.
    cells = {(j-r, -r): int(word[r*r+j])
             for r in range(rows) for j in range(2*r+1)}
    patterns = []
    for x, y in cells:
        t = ((x, y+1), (x-1, y), (x, y), (x+1, y))
        if all(p in cells for p in t):
            patterns.append(tuple(cells[p] for p in t))
    assert len(patterns) == (rows-1)**2
    return patterns


def prefix_orbits(q, rows):
    groups = Counter()
    rejected = 0
    for digits in itertools.product(range(q), repeat=rows*rows):
        word = ''.join(map(str, digits))
        codes = independent_patterns(word, q, rows)
        if len(set(codes)) != len(codes):
            rejected += 1
            continue
        groups[canonical(word, rows)] += 1
    assert sum(groups.values()) + rejected == q**(rows*rows)
    # Independently reconstruct all images, including color stabilizers.
    for word, multiplicity in groups.items():
        images = set()
        for perm in itertools.permutations(map(str, range(q))):
            changed = ''.join(perm[int(c)] for c in word)
            images.add(changed)
            images.add(''.join(changed[r*r:(r+1)**2][::-1]
                               for r in range(rows)))
        assert len(images) == multiplicity
    return groups, rejected


def count(binary, q, rows, prefix, seconds=None):
    args = [str(binary), '--colors', str(q), '--rows', str(rows)]
    if prefix:
        args += ['--prefix', prefix]
    if seconds is not None:
        args += ['--seconds', str(seconds)]
    run = subprocess.run(args, text=True, capture_output=True)
    if run.returncode not in (0, 1):
        raise RuntimeError(run.stderr)
    fields = dict(item.split('=', 1) for item in run.stdout.strip().split())
    if seconds is None:
        assert fields['status'] == 'COMPLETE'
    return int(fields['exact_count_completed_interval']), fields


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--colors', type=int, default=3, choices=(2, 3))
    parser.add_argument('--rows', type=int, default=5)
    parser.add_argument('--prefix-rows', type=int, default=3, choices=(1, 2, 3))
    parser.add_argument('--seconds', type=float, default=240)
    parser.add_argument('--output', type=Path,
                        default=ROOT/'experiments/exact_algo_census_results.json')
    args = parser.parse_args()
    if not args.prefix_rows <= args.rows <= args.colors**2+1 or args.seconds <= 0:
        parser.error('require prefix rows <= rows <= colors squared + 1 and seconds > 0')
    binary = Path(tempfile.mkdtemp(prefix='tboards-exact-census-'))/'counter'
    subprocess.run(['g++', '-O3', '-std=c++23', '-Wall', '-Wextra', '-Wpedantic', '-Werror',
                    str(ROOT/'experiments/exact_algo_count.cpp'), '-o', str(binary)],
                   check=True)
    # Smaller checks use no prefix quotient at all.
    assert count(binary, 2, 5, '')[0] == 168
    assert count(binary, 3, 4, '')[0] == 28174794
    groups, rejected = prefix_orbits(args.colors, args.prefix_rows)
    print(f'prefix_orbits={len(groups)} labeled_valid_prefixes={sum(groups.values())} '
          f'rejected_prefixes={rejected}', flush=True)
    data = dict(colors=args.colors, rows=args.rows, prefix_rows=args.prefix_rows,
                total_prefix_orbits=len(groups), labeled_valid_prefixes=sum(groups.values()),
                rejected_prefixes=rejected, results=[], status='INCOMPLETE')
    start = time.monotonic()
    total = 0
    for i, (prefix, multiplicity) in enumerate(sorted(groups.items())):
        if time.monotonic()-start >= args.seconds:
            break
        subtotal, stats = count(binary, args.colors, args.rows, prefix,
                                args.seconds-(time.monotonic()-start))
        if stats['status'] != 'COMPLETE':
            data['interrupted_prefix'] = prefix
            data['interrupted_stats'] = stats
            break
        total += multiplicity*subtotal
        data['results'].append(dict(prefix=prefix, orbit_size=multiplicity,
                                    completions=subtotal, stats=stats))
        if (i+1) % 100 == 0:
            data['count_completed_orbits'] = total
            data['elapsed'] = time.monotonic()-start
            args.output.write_text(json.dumps(data, indent=2)+'\n')
            print(f'completed={i+1}/{len(groups)} partial_count={total} '
                  f'elapsed={time.monotonic()-start:.2f}', flush=True)
    if len(data['results']) == len(groups):
        data['status'] = 'COMPLETE'
    data['count_completed_orbits'] = total
    data['elapsed'] = time.monotonic()-start
    args.output.write_text(json.dumps(data, indent=2)+'\n')
    print(f"status={data['status']} count_completed_orbits={total} "
          f"elapsed={data['elapsed']:.3f} output={args.output}", flush=True)
    if data['status'] != 'COMPLETE':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
