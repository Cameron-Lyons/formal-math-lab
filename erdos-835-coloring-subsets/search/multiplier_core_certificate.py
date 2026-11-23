"""Regenerate the order-eight multiplier obstruction checked by MultiplierCore.lean.

Run with Python 3.10+ and the cadical executable in the project's Lean toolchain.
--classify-only enumerates the cores and checks the degree and additive criteria
without running a SAT solver. The Lean theorem checks the resulting certificate
without assuming correctness of the enumeration or the external solver.
"""

import argparse
from collections import defaultdict
from functools import cache
from itertools import combinations
import json
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory


POINTS = range(17)
QUADS = list(combinations(POINTS, 4))
TRIPLES = list(combinations(POINTS, 3))


def scale(block):
    return tuple(sorted(9 * x % 17 for x in block))


def translate(block, shift):
    return tuple(sorted((x + shift) % 17 for x in block))


def scalar_orbit(block):
    result = [block]
    later = scale(block)
    while later != block:
        result.append(later)
        later = scale(later)
    return result


@cache
def translation_rep(block):
    return min(translate(block, step) for step in POINTS)


def enumerate_cores(atoms):
    """Select one row per affine shape, forbidding repeated triples."""
    triple_index = {triple: i for i, triple in enumerate(TRIPLES)}
    by_shape = defaultdict(list)
    for base in atoms:
        orbit = scalar_orbit(base)
        shapes = list(map(translation_rep, orbit))
        triples = [t for block in orbit for t in combinations(block, 3)]
        if len(set(shapes)) != len(shapes) or len(set(triples)) != len(triples):
            continue
        mask = sum(1 << triple_index[t] for t in triples)
        by_shape[min(shapes)].append((mask, orbit))
    groups = sorted(by_shape.values(), key=len)

    def visit(remaining, used, chosen):
        if not remaining:
            yield frozenset(block for orbit in chosen for block in orbit)
            return
        # Branch on the group with the fewest compatible choices.
        choices = [(i, [r for r in groups[i] if not r[0] & used]) for i in remaining]
        index, rows = min(choices, key=lambda pair: len(pair[1]))
        rest = [i for i in remaining if i != index]
        for mask, orbit in rows:
            yield from visit(rest, mask | used, chosen + [orbit])

    yield from visit(list(range(len(groups))), 0, [])


def certificate(cores, atoms):
    """Pair each clause with its finite geometric evidence."""
    codes = {}
    blocks = []
    for i, base in enumerate(atoms):
        for exponent, block in enumerate(scalar_orbit(base)):
            codes[block] = 8 * i + exponent
        block = base
        for _ in range(8):
            blocks.append(block)
            block = scale(block)

    clauses = {}

    def add(kind, occurrences, exceptions=()):
        occurrences = list(occurrences)
        sign = 1 if kind[0] in (0, 3) else -1
        literals = tuple(sorted({sign * (codes[b] // 8 + 1) for b in occurrences}))
        rule = [kind, [codes[b] for b in occurrences], [codes[b] for b in exceptions]]
        clauses.setdefault(literals, rule)

    affine_shapes = sorted({min(map(translation_rep, scalar_orbit(b))) for b in atoms})
    for base in affine_shapes:
        translates = [translate(base, d) for d in POINTS]
        add([0, *base], translates)
        for (i, a), (j, b) in combinations(enumerate(translates), 2):
            add([1, j-i], [a, b])
    for triple in sorted({min(scalar_orbit(t)) for t in TRIPLES}):
        through = [tuple(sorted((*triple, x))) for x in POINTS if x not in triple]
        for pair in combinations(through, 2):
            add([2], pair)

    by_pair = defaultdict(list)
    for block in QUADS:
        for pair in combinations(block, 2):
            by_pair[pair].append(block)
    additive = frozenset(b for b in QUADS if sum(b) % 17 == 0)
    failures = 0
    for core in cores:
        violations = []
        for pair, through in by_pair.items():
            exceptions = [b for b in through if b in core]
            if len(exceptions) < 6:
                others = [b for b in through if b not in core]
                size = len({codes[b] // 8 for b in others})
                violations.append((size, pair, others, exceptions))
        if violations:
            failures += 1
            _, pair, others, exceptions = min(violations)
            add([3, *pair], others, exceptions)
        else:
            assert core == additive
            add([4], sorted(core))
    print(f"{len(cores)} cores, {failures} violate the degree bound, "
          f"{len(cores) - failures} additive")
    return blocks, clauses


def trace_core(path, count):
    """Trace the empty clause backwards to original clauses used in its proof."""
    dependencies = {}
    with path.open() as proof:
        for line in proof:
            words = line.split()
            if words[1] == "d":
                continue
            row = list(map(int, words))
            split = row.index(0)
            clause_id = row[0]
            dependencies[clause_id] = [abs(x) for x in row[split + 1:-1]]
            if split == 1:
                break
        else:
            raise ValueError("Missing empty clause")
    used = {clause_id}
    for clause_id in reversed(dependencies):
        if clause_id in used:
            used.update(dependencies[clause_id])
    return [i - 1 for i in sorted(used) if i <= count]


def solve(solver, atom_count, clauses, path):
    source = path.with_suffix(".cnf")
    with source.open("w") as output:
        print("p cnf", atom_count, len(clauses), file=output)
        for clause in clauses:
            print(*clause, 0, file=output)
    result = subprocess.run([solver, "--plain", "--lrat", "--no-binary", source, path],
                            stdout=subprocess.DEVNULL)
    if result.returncode != 20:
        raise RuntimeError(f"CaDiCaL returned {result.returncode}, expected UNSAT (20)")


def write_json(path, data):
    path.write_text(json.dumps(data, separators=(",", ":")) + "\n")


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--solver", default="cadical", help="CaDiCaL executable")
    cli.add_argument("--output", type=Path, default=Path("certificates"))
    cli.add_argument("--classify-only", action="store_true")
    args = cli.parse_args()
    atoms = sorted({min(scalar_orbit(block)) for block in QUADS})
    cores = list(enumerate_cores(atoms))
    assert len(atoms) == 302 and all(len(core) == 140 for core in cores)
    blocks, rules = certificate(cores, atoms)
    if args.classify_only:
        return
    output = args.output
    output.mkdir(parents=True, exist_ok=True)
    clauses = list(rules)
    with TemporaryDirectory() as tmp:
        trace = Path(tmp) / "multiplier8.lrat"
        solve(args.solver, len(atoms), clauses, trace)
        for _ in range(3):
            retained = trace_core(trace, len(clauses))
            if len(retained) == len(clauses):
                break
            clauses = [clauses[i] for i in retained]
            solve(args.solver, len(atoms), clauses, trace)
        shutil.copyfile(trace, output / trace.name)
    write_json(output / "multiplier8-sat.json",
               [[[abs(v)-1, v > 0] for v in clause] for clause in clauses])
    write_json(output / "multiplier8-blocks.json", blocks)
    write_json(output / "multiplier8-rules.json", [rules[c] for c in clauses])
    print(f"Wrote {len(clauses)} clauses with {len(atoms)} atoms to {output}")


if __name__ == "__main__":
    main()
