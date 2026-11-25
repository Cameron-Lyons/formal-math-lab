"""Generate the larger Lean certificate from audited representatives.

Only generated explicit data is trusted after Lean checks it. Python's sorting,
orbit construction, and search are outside the proof's trusted computing base.
"""

import itertools
import json
from pathlib import Path

SEEDS_PER_BATCH = 32
LANES = 4
BOARDS_PER_BLOCK = 128


def board_literal(rows):
    return "[\n" + ",\n".join("  [" + ",".join(row) + "]" for row in rows) + "\n]"


def options():
    return [
        "set_option Elab.async false",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "",
        "namespace TBoards.Extended",
        "",
    ]


def main():
    records = json.loads(Path("extended_seeds.json").read_text())
    directory = Path("Extended")
    directory.mkdir(exist_ok=True)
    entries = []
    batches = (len(records) + SEEDS_PER_BATCH - 1) // SEEDS_PER_BATCH
    for batch in range(batches):
        parent = (
            f"Extended.Batch{batch - LANES:03}" if batch >= LANES else "CertifiedFamily"
        )
        lines = [
            f"import {parent}",
            "",
            "/- Generated from extended_seeds.json. Published seeds 0–4:",
            "   Qiyuan Ma, DOI 10.5281/zenodo.23631079, CC-BY-4.0. -/",
            "",
            *options(),
        ]
        for record in records[batch * SEEDS_PER_BATCH : (batch + 1) * SEEDS_PER_BATCH]:
            i = record["index"]
            rows = record["rows"]
            lines += [f"def seed{i:04} : Board := {board_literal(rows)}", ""]
            for reflection in [False, True]:
                suffix = "r" if reflection else "n"
                board = f"seed{i:04}.map List.reverse" if reflection else f"seed{i:04}"
                lines += [
                    f"def cert{i:04}{suffix} : CertifiedBoard :=",
                    f"  ⟨{board}, by apply FastValid.valid; decide +kernel⟩",
                    "",
                ]
                oriented = [row[::-1] if reflection else row for row in rows]
                for pi, perm in enumerate(itertools.permutations("012")):
                    transformed = [
                        "".join(perm[int(c)] for c in row) for row in oriented
                    ]
                    flat = "".join(transformed)
                    entries.append(
                        (
                            int(flat, 3),
                            f"renameCertified cert{i:04}{suffix} {pi}",
                            transformed,
                        )
                    )
        lines += ["end TBoards.Extended", ""]
        (directory / f"Batch{batch:03}.lean").write_text("\n".join(lines))
    entries.sort()
    if len({key for key, _, _ in entries}) != len(entries):
        raise ValueError("Duplicate numeric board fingerprints")
    expected = json.loads(Path("extended_family.json").read_text())
    if [rows for _, _, rows in entries] != expected:
        raise ValueError(
            "Generated order differs from the independently audited family"
        )
    lines = [
        f"import Extended.Batch{i:03}" for i in range(max(0, batches - LANES), batches)
    ]
    lines += ["", *options()]
    block_count = (len(entries) + BOARDS_PER_BLOCK - 1) // BOARDS_PER_BLOCK
    for block in range(block_count):
        subset = entries[block * BOARDS_PER_BLOCK : (block + 1) * BOARDS_PER_BLOCK]
        lines += [
            f"def boards{block:03} : List CertifiedBoard := [",
            ",\n".join("  " + expr for _, expr, _ in subset),
            "]",
            "",
            f"def codes{block:03} : List Nat := [",
            ",\n".join("  " + str(key) for key, _, _ in subset),
            "]",
            "",
            f"theorem codes{block:03}_correct :",
            f"    (certifiedValues boards{block:03}).map boardCode = codes{block:03} := by decide +kernel",
            "",
            f"def block{block:03} : CodeBlock :=",
            f"  ⟨boards{block:03}, codes{block:03}, codes{block:03}_correct⟩",
            "",
        ]
    lines += [
        "def blocks : List CodeBlock := [",
        ",\n".join(f"  block{i:03}" for i in range(block_count)),
        "]",
        "",
        "end TBoards.Extended",
        "",
    ]
    (directory / "Blocks.lean").write_text("\n".join(lines))
    Path("Extended.lean").write_text("import Extended.Blocks\n")
    n = len(entries)
    lines = [
        "import Extended",
        "",
        "set_option Elab.async false",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "",
        "namespace TBoards",
        "",
        "/-- The larger explicit family, whose entries all carry validity proofs. -/",
        "def extendedFamily : List Board := certifiedValues (Extended.blocks.flatMap CodeBlock.boards)",
        "",
        f"theorem extendedFamily_length : extendedFamily.length = {n} := by",
        "  have h := congrArg List.length (codeBlocks_correct Extended.blocks)",
        "  simp only [List.length_map] at h",
        "  exact h.trans (by decide +kernel)",
        "",
        "theorem extendedFamily_nodup : extendedFamily.Nodup := by",
        "  apply nodup_of_increasing_codes",
        "  change increasing ((certifiedValues (Extended.blocks.flatMap CodeBlock.boards)).map boardCode) = true",
        "  rw [codeBlocks_correct]",
        "  decide +kernel",
        "",
        "theorem extendedFamily_valid : ∀ b ∈ extendedFamily, Valid b :=",
        "  certifiedValues_valid _",
        "",
        f"/-- At least {n} distinct labeled three-color T boards exist. -/",
        f"theorem at_least_{n} :",
        f"    ∃ f : Fin {n} → Board, (∀ i, Valid (f i)) ∧",
        "      (∀ i j, f i = f j → i = j) := by",
        f"  exact injective_family_of_list extendedFamily {n}",
        f"    (by rw [extendedFamily_length]; exact Nat.le_refl {n})",
        "    extendedFamily_nodup extendedFamily_valid",
        "",
        "end TBoards",
        "",
        f"#print axioms TBoards.at_least_{n}",
        "",
    ]
    Path("ExtendedCertificates.lean").write_text("\n".join(lines))
    print(
        f"Generated {batches} orientation batches and {block_count} code blocks for {n} boards."
    )


if __name__ == "__main__":
    main()
