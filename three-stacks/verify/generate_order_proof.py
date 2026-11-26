"""Regenerate the Lean order proof from the published deck's CNF and a trimmed all-RUP LRAT trace."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations, permutations
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterable

# Arrival order, also defined as ThreeStacks.published in ThreeStacks/Model.lean.
PUBLISHED = (6, 3, 12, 8, 17, 5, 2, 11, 7, 19, 14, 10, 4, 18, 13, 21, 16, 9, 20, 15, 1)
Order = tuple[bool, int, int]


@dataclass
class Original:
    lits: list[int]
    kind: str
    cards: tuple[int, ...]


def clauses() -> tuple[dict[int, Original], dict[int, Order]]:
    cards = list(range(1, 22))
    pairs: dict[Order, int] = {}
    labels: dict[int, Order] = {}
    for row, (a, b) in enumerate(combinations(cards, 2), 1):
        for layer, offset in ((False, 0), (True, 210)):
            var = row + offset
            pairs[layer, a, b] = var
            pairs[layer, b, a] = -var
            labels[var] = layer, a, b
            labels[-var] = layer, b, a
    original: dict[int, Original] = {}

    def put(kind: str, lits: list[int], triple: tuple[int, ...] = ()) -> None:
        original[len(original) + 1] = Original(lits, kind, triple)

    for a, b, c in combinations(cards, 3):
        for layer in (False, True):
            cycle = [pairs[layer, a, b], pairs[layer, b, c], pairs[layer, c, a]]
            put("cycle", cycle)
            put("cycle", [-x for x in cycle])
    for a, b, c in combinations(PUBLISHED, 3):
        put("entering", [-pairs[False, c, a], -pairs[False, a, b]], (a, b, c))
    for a, b, c in permutations(cards, 3):
        put(
            "middle",
            [
                -pairs[False, a, b],
                -pairs[False, b, c],
                -pairs[True, c, a],
                -pairs[True, a, b],
            ],
            (a, b, c),
        )
    for c, a, b in combinations(cards, 3):
        put("leaving", [-pairs[True, a, b], -pairs[True, b, c]], (a, b, c))
    return original, labels


@dataclass
class Unit:
    name: str
    literal: int
    reason: int
    args: list[str]


@dataclass
class Proof:
    units: list[Unit]
    conflict: int
    args: list[str]


def trim_step(
    formula: dict[int, list[int]], goal: list[int], hints: list[int]
) -> Proof:
    """Follow unit propagation and keep just the units used in the contradiction."""
    known = {-literal: f"z{i}" for i, literal in enumerate(goal)}
    units: list[Unit] = []
    for hint in hints:
        clause = formula[hint]
        if any(literal in known for literal in clause):
            raise ValueError(f"Reason {hint} already has a true literal")
        unassigned = [literal for literal in clause if -literal not in known]
        if len(unassigned) > 1:
            raise ValueError(f"Reason {hint} does not give a unit or a conflict")
        args = [known.get(-literal, "bad") for literal in clause]
        if not unassigned:
            needed = set(args)
            keep: list[Unit] = []
            for unit in reversed(units):
                if unit.name in needed:
                    needed.update(unit.args)
                    keep.append(unit)
            return Proof(list(reversed(keep)), hint, args)
        pivot = unassigned[0]
        name = f"u{len(units)}"
        known[pivot] = name
        units.append(Unit(name, pivot, hint, args))
    raise ValueError("LRAT step ended without a conflict")


def read_trace(
    lrat: Path, formula: dict[int, list[int]]
) -> tuple[dict[int, Proof], int]:
    proofs: dict[int, Proof] = {}
    for line in lrat.read_text().splitlines():
        parts = line.split()
        if parts[1] == "d":
            continue
        row = list(map(int, parts))
        idx = row.index(0)
        number, goal, hints = row[0], row[1:idx], row[idx + 1 : -1]
        if number in formula or not hints or min(hints) <= 0 or row[-1] != 0:
            raise ValueError(f"Invalid RUP record for clause {number}")
        proofs[number] = trim_step(formula, goal, hints)
        formula[number] = goal
    if not proofs:
        raise ValueError("The LRAT trace has no derived clauses")
    last = next(reversed(proofs))
    if formula[last]:
        raise ValueError("Final derived clause is not empty")
    return proofs, last


def emit(evidence: Path, lrat: Path, output: Path) -> None:
    original, labels = clauses()
    formula = {i: c.lits for i, c in original.items()}
    actual = evidence / "verify/published/pv21.cnf"
    cnf = [
        list(map(int, line.split()[:-1]))
        for line in actual.read_text().splitlines()
        if not line.startswith("p ")
    ]
    if cnf != list(formula.values()):
        raise ValueError("Archived CNF differs from the reconstructed order clauses")

    proofs, last = read_trace(lrat, formula)
    used = {last}
    for i, proof in reversed(proofs.items()):
        if i in used:
            used.add(proof.conflict)
            used.update(unit.reason for unit in proof.units)
    originals = [i for i in original if i in used]
    derived = [i for i in proofs if i in used]
    print(
        f"{len(originals)} source clauses, {len(derived)} learned clauses, "
        f"{sum(len(proofs[i].units) for i in derived)} unit inferences"
    )

    prefix = "ThreeStacks.OrderProof."
    output.mkdir(parents=True, exist_ok=True)

    def lit(x: int) -> str:
        layer, a, b = labels[x]
        return f"Before w {str(layer).lower()} {a} {b}"

    def theorem(i: int) -> str:
        signature = " → ".join([*(lit(-x) for x in formula[i]), "False"])
        return f"theorem c{i} (w : Witness) : {signature} :="

    def write(name: str, sources: Iterable[str], lines: list[str]) -> None:
        text = "\n".join(f"import {source}" for source in sources)
        text += "\n\n/- Generated natural-deduction proof. See verify/generate_order_proof.py. -/\n"
        text += "set_option maxRecDepth 15000\nset_option maxHeartbeats 8000000\n\nnamespace ThreeStacks.OrderProof\n\n"
        text += "\n".join(lines) + "\n\nend ThreeStacks.OrderProof\n"
        (output / (name + ".lean")).write_text(text)

    lines: list[str] = []
    for card in range(1, 22):
        membership = ".head _"
        for _ in range(card - 1):
            membership = f".tail _ ({membership})"
        lines.append(
            f"private theorem mem{card} : {card} ∈ target 21 := {membership}\n"
        )
    for x in range(1, 421):
        layer, a, b = labels[x]
        lines.append(
            f"theorem t{x} (w : Witness) : {lit(x)} ∨ {lit(-x)} :=\n"
            f"  alternatives w {str(layer).lower()} {a} {b} mem{a} mem{b} (by decide)\n"
        )
    write("Alternatives", ["ThreeStacks.CertificateBase"], lines)
    base_chunks: list[str] = []
    for start in range(0, len(originals), 512):
        name = f"Clauses{start // 512:02}"
        base_chunks.append(prefix + name)
        lines = []
        for i in originals[start : start + 512]:
            clause = original[i]
            names = [f"z{j}" for j in range(len(clause.lits))]
            if clause.kind == "cycle":
                edges = {}
                for literal, param in zip(clause.lits, names, strict=True):
                    _, a, b = labels[-literal]
                    edges[a, b] = param
                layer = labels[clause.lits[0]][0]
                a, b = next(iter(edges))
                c = next(y for x, y in edges if x == b)
                body = f"cycle w {str(layer).lower()} {a} {b} {c} {edges[a, b]} {edges[b, c]} {edges[c, a]}"
            else:
                a, b, c = clause.cards
                args = names.copy()
                if clause.kind == "entering":
                    args = ["(by decide)", "(by decide)", *args]
                if clause.kind == "leaving":
                    args += ["(by decide)", "(by decide)"]
                body = f"w.{clause.kind} {a} {b} {c} " + " ".join(args)
            lines.extend((theorem(i), "  fun " + " ".join(names) + " => " + body, ""))
        write(name, ["ThreeStacks.CertificateBase"], lines)
    for start in range(0, len(derived), 75):
        idx = start // 75
        name = f"Learned{idx:02}"
        sources = (
            [f"{prefix}Learned{idx - 1:02}"]
            if idx
            else [prefix + "Alternatives", *base_chunks]
        )
        lines = []
        for i in derived[start : start + 75]:
            proof = proofs[i]
            lines.append(theorem(i))
            if formula[i]:
                used_names = set(proof.args)
                used_names.update(v for unit in proof.units for v in unit.args)
                names = [
                    f"z{j}" if f"z{j}" in used_names else "_"
                    for j in range(len(formula[i]))
                ]
                lines.append("  fun " + " ".join(names) + " =>")
            for unit in proof.units:
                rule = "forceLeft" if unit.literal > 0 else "forceRight"
                term = f"c{unit.reason} w " + " ".join(unit.args)
                lines.append(
                    f"  have {unit.name} := {rule} (t{abs(unit.literal)} w) (fun bad => {term})"
                )
            lines.append(f"  c{proof.conflict} w " + " ".join(proof.args) + "\n")
        write(name, sources, lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--evidence-root",
        required=True,
        type=Path,
        help="extracted three-stack-bound directory",
    )
    parser.add_argument("lrat", type=Path, help="LRAT file produced by drat-trim -L")
    parser.add_argument(
        "output", type=Path, help="destination directory for generated Lean modules"
    )
    args = parser.parse_args()
    emit(args.evidence_root, args.lrat, args.output)
