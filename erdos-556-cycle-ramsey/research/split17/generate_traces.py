"""Rebuild the eighteen decision trees for the spokes of K17 minus K4.

The graph representatives and their classifications are already checked in
Lean. This optional generator uses python-sat to discover cycles that cover
all spoke assignments. Its output is a Lean source file whose checker only
uses the path from a decision-tree root to a leaf and the cycle at that leaf.
"""
import argparse
from itertools import combinations, permutations
from pathlib import Path
import re

from pysat.solvers import Solver


CORE = 13
OUTSIDE = 4
VARIABLES = CORE * OUTSIDE
ORDER = CORE + OUTSIDE


def graph_rows(code, color):
    rows = [0] * CORE
    for j in range(CORE):
        for i in range(j):
            bit = j * (j - 1) // 2 + i
            if ((code >> bit) & 1) == color:
                rows[i] |= 1 << j
                rows[j] |= 1 << i
    return rows


def find_path(rows, start, length, end=None):
    """Find a path with the requested endpoints, or a cycle through start."""
    path = [start]
    full = (1 << len(rows)) - 1

    def visit(vertex, remaining, unused):
        if remaining == 0:
            if end is None:
                return bool(rows[vertex] & (1 << start))
            return vertex == end
        choices = rows[vertex] & unused
        if end is None:
            choices &= ~((1 << start) - 1)
        elif remaining == 1:
            choices &= 1 << end
        else:
            choices &= ~(1 << end)
        while choices:
            bit = choices & -choices
            choices ^= bit
            next_vertex = bit.bit_length() - 1
            path.append(next_vertex)
            if visit(next_vertex, remaining - 1, unused ^ bit):
                return True
            path.pop()
        return False

    return tuple(path) if visit(start, length, full ^ (1 << start)) else None


def find_cycle(rows):
    for start in range(len(rows) - 8):
        cycle = find_path(rows, start, 8)
        if cycle is not None:
            return cycle
    return None


def spoke_mask(cycle):
    result = 0
    for x, y in zip(cycle, cycle[1:] + cycle[:1]):
        i, j = sorted((x, y))
        if j >= CORE:
            result |= 1 << (CORE * (j - CORE) + i)
    return result


def pack_cycle(cycle):
    return sum(v << (5 * i) for i, v in enumerate(cycle))


def collect_cycles(core):
    base = [graph_rows(core, k) for k in (0, 1)]
    clauses = []
    seen = set()
    with Solver(name="cadical195") as solver:
        def add(color, cycle):
            mask = spoke_mask(cycle)
            if (color, mask) in seen:
                return False
            seen.add((color, mask))
            clauses.append((color, mask, pack_cycle(cycle)))
            sign = 1 if color == 0 else -1
            solver.add_clause([sign * (i + 1) for i in range(VARIABLES) if mask & (1 << i)])
            return True

        for color in (0, 1):
            for a, b in combinations(range(CORE), 2):
                path = find_path(base[color], a, 7, b)
                if path is not None:
                    for outside in range(CORE, ORDER):
                        add(color, (outside,) + path)

        # Each proposed assignment either contains a cycle or is a counterexample.
        while solver.solve():
            model = solver.get_model()
            rows = [r.copy() + [0] * OUTSIDE for r in base]
            for j in range(CORE, ORDER):
                for i in range(CORE):
                    color = int(model[(j - CORE) * CORE + i] > 0)
                    rows[color][i] |= 1 << j
                    rows[color][j] |= 1 << i
            found = False
            for color in (0, 1):
                cycle = find_cycle(rows[color])
                if cycle is None:
                    continue
                for permutation in permutations(range(CORE, ORDER)):
                    image = tuple(v if v < CORE else permutation[v - CORE] for v in cycle)
                    found |= add(color, image)
            if not found:
                raise RuntimeError(f"Uncovered spoke assignment: {model}")
    return clauses


def decision_tree(clauses, zero=0, one=0):
    scores = [0] * VARIABLES
    unit = None
    for color, mask, cycle in clauses:
        assigned, opposite = (zero, one) if color == 0 else (one, zero)
        if mask & opposite:
            continue
        undecided = mask & ~assigned
        if undecided == 0:
            return f"(.cycle {str(bool(color)).lower()} {cycle:#x})"
        if undecided.bit_count() == 1:
            if unit is None:
                unit = undecided
        elif unit is None:
            weight = 64 >> min(undecided.bit_count(), 6)
            while undecided:
                bit = undecided & -undecided
                scores[bit.bit_length() - 1] += weight
                undecided ^= bit
    bit = unit if unit is not None else 1 << max(range(VARIABLES), key=scores.__getitem__)
    if bit & (zero | one):
        raise RuntimeError("Decision tree encountered a satisfying assignment")
    left = decision_tree(clauses, zero | bit, one)
    right = decision_tree(clauses, zero, one | bit)
    return f"(.branch {bit.bit_length() - 1}\n {left}\n {right})"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="destination for the reconstructed Proofs.lean")
    args = parser.parse_args()
    project = Path(__file__).resolve().parents[2]
    source = project / "Ramsey556" / "Split17"
    data = (source / "Data.lean").read_text()
    block = data.split("private def graphs13", 1)[1].split("]", 1)[0]
    cores = [int(value, 16) for value in re.findall(r"0x[0-9a-f]+", block)]
    if len(cores) != 18:
        raise ValueError("Expected 18 thirteen-vertex representatives")
    original = (source / "Proofs.lean").read_text()
    prefix = original.split("private noncomputable def trace0", 1)[0]
    suffix = original[original.index("/-- Every coloring of the spokes"):]
    output = [prefix]
    for i, core in enumerate(cores):
        trace = decision_tree(collect_cycles(core))
        output.append(f"private noncomputable def trace{i} : Trace :=\n {trace}\n\n")
        output.append(f"private theorem valid{i} : check (core13 {i}) (fun _ => 0) trace{i} = true := by decide +kernel\n\n")
    args.output.write_text("".join(output) + suffix)


if __name__ == "__main__":
    main()
