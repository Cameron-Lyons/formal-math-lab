# Five 30-sided Go First Dice (5 d30, labels 1–150): modulo-4 obstruction and mirrored-block exclusion — Lean 4 proofs

**Status: whether five 30-sided Go First Dice exist remains open.** Can five fair 30-sided dice be labeled with the distinct integers $1, 2, \ldots, 150$ so that, when rolled independently, all $5! = 120$ strict ordering permutations of the five players occur with equal probability (each appearing $30^5 / 120 = 202{,}500$ times)? The Go First Dice project lists five 30-sided dice (`5 d30`) as open; Paul Meyer constructed five 60-sided Go First Dice (`5 d60`).

This Lean 4 project proves a **general necessary modulo-4 condition** (`FiveDice.EqualCuts.needs_distinct_residues`), proves in Lean that **15 mirrored permutation blocks cannot yield a fair labeling** (`FiveDice.Mirrored.no_fifteen_mirrored`), proves soundness/completeness of the exact ranking-count checker (`FiveDice.check30_iff`), and kernel-verifies Paul Meyer's 60-sided construction (`FiveDice.meyer60_fair`).

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Five 30-sided Go First Dice** (`5 d30`, permutation-fair dice, labels `1..150`, all 120 rankings equally likely with 202,500 rolls each), Harshbarger / Go First Dice open questions (`#d30`), Gavenčiak–Haeupler–Rozhoň (`arXiv:2610.15421`, §1.2) |
| **Status** | **Partial results (necessary modulo-4 condition and mirrored-block exclusion).** Unrestricted existence of five 30-sided Go First Dice remains open. |
| **Main Lean theorems** | `FiveDice.EqualCuts.needs_distinct_residues` ([EqualCuts.lean](EqualCuts.lean)), `FiveDice.Mirrored.no_fifteen_mirrored` ([MirroredObstruction.lean](MirroredObstruction.lean)), `FiveDice.check30_iff` ([FiveDice.lean](FiveDice.lean)), `FiveDice.meyer60_fair` ([Meyer60.lean](Meyer60.lean)) |
| **Verification** | `lake build` (Lean 4.36.0, stdlib only; `check30_iff`, `needs_distinct_residues`, and `meyer60_fair` are kernel-checked; `no_fifteen_mirrored` uses `native_decide` for 5,400 finite inequalities) |
| **Prior-art status** | Checked **24 November 2026**: an earlier exhaustive search by the Go First Dice team already excluded all column-grouped labelings (which include the 15 mirrored blocks); priority of the modulo-4 cut condition is unconfirmed. See [PRIOR_ART.md](../PRIOR_ART.md#five-30-sided-go-first-dice). |

## Lean results

* **Exact fairness checker (`FiveDice.check30_iff`, [FiveDice.lean](FiveDice.lean)):** write the owner of each face in increasing label order using die indices $0, 1, 2, 3, 4$. A roll producing ranking `[2, 0, 1, 4, 3]` corresponds to picking one occurrence of each die in that order. Lean proves the checker accepts a labeling if and only if every one of the 120 rankings occurs exactly 202,500 times.
* **Necessary modulo-4 condition (`FiveDice.EqualCuts.needs_distinct_residues`, [EqualCuts.lean](EqualCuts.lean)):** at each face of a die, count how many higher labels belong to each of the four opponents. In any permutation-fair labeling of five 30-sided dice, every die must have at least one face where two opponents' counts of higher labels are **not congruent modulo 4**.
* **Mirrored permutation blocks excluded (`FiveDice.Mirrored.no_fifteen_mirrored`, [MirroredObstruction.lean](MirroredObstruction.lean)):** 15 consecutive blocks, each consisting of a 5-die permutation followed by its reverse, cannot yield a fair labeling (Lean proof of a special case of the Go First Dice team's column-grouped exclusion).
* **Verified 60-sided example (`FiveDice.meyer60_fair`, [Meyer60.lean](Meyer60.lean)):** kernel-checks Paul Meyer's five 60-sided Go First Dice, verifying all 120 rankings occur exactly $60^5 / 120 = 6{,}480{,}000$ times.

## Reproduce

Run from this directory with Lean **4.36.0** (standard library only):

```sh
lake build
```

## References

* [Go First Dice — Open Questions (`#d30`)](http://gofirstdice.ericharshbarger.org/doku.php?id=open_questions#d30) · [Column-paired / homogeneous search counts](http://gofirstdice.ericharshbarger.org/doku.php?id=homogeneous_solutions#column_paired)
* [Gavenčiak, Haeupler, and Rozhoň, `arXiv:2610.15421v1`, §1.2](https://arxiv.org/html/2610.15421v1#S1.SS2)
* [The Dice Lab — Paul Meyer's 5 d60 Go First Dice](https://www.mathartfun.com/thedicelab.com/GFD5.html)
* [Dated prior-art audit](../PRIOR_ART.md#five-30-sided-go-first-dice)
