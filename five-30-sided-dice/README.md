# Five 30-sided Go First Dice

**Go First Dice** are sets of specially numbered dice that let a group of players decide a completely fair turn order—1st, 2nd, 3rd, ..., last—with a single simultaneous roll. To avoid ties, all faces across all dice carry distinct integers $1, 2, \ldots, N$.

For five 30-sided dice (`5 d30`), can we partition the integers $1, 2, \ldots, 150$ into five 30-face dice so that rolling them independently produces all $5! = 120$ strict orderings of the five players with exact equal probability? Out of $30^5 = 24{,}300{,}000$ equally likely rolls, each of the 120 rankings would have to appear exactly $30^5 / 120 = 202{,}500$ times. While Paul Meyer constructed five 60-sided Go First Dice (`5 d60`), the Go First Dice project lists `5 d30` as open.

The Lean 4 proofs here establish two structural obstructions for `5 d30`—a necessary modulo-4 face-count condition (`FiveDice.EqualCuts.needs_distinct_residues`) and an exclusion of labelings built from 15 mirrored permutation blocks (`FiveDice.Mirrored.no_fifteen_mirrored`)—along with a formally verified exact fairness checker (`FiveDice.check30_iff`) and a pure kernel check of Paul Meyer's 60-sided dice (`FiveDice.meyer60_fair`). Whether unrestricted five 30-sided Go First Dice exist remains open.

| Field | Summary |
| --- | --- |
| Problem | Five 30-sided Go First Dice (`5 d30`, labels `1..150`, all 120 rankings occurring 202,500 times), Harshbarger open questions (`#d30`), Gavenčiak, Haeupler, and Rozhoň (`arXiv:2610.15421`, §1.2) |
| Status | Partial results (modulo-4 condition and mirrored-block exclusion). Unrestricted existence of five 30-sided Go First Dice remains open. |
| Main theorems | `FiveDice.EqualCuts.needs_distinct_residues` ([EqualCuts.lean](EqualCuts.lean)), `FiveDice.Mirrored.no_fifteen_mirrored` ([MirroredObstruction.lean](MirroredObstruction.lean)), `FiveDice.check30_iff` ([FiveDice.lean](FiveDice.lean)), `FiveDice.meyer60_fair` ([Meyer60.lean](Meyer60.lean)) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; `check30_iff`, `needs_distinct_residues`, and `meyer60_fair` are kernel-checked; `no_fifteen_mirrored` uses `native_decide` for 5,400 finite inequalities) |
| Prior art | Checked 24 November 2026: an earlier exhaustive search by the Go First Dice team already ruled out all column-grouped labelings (which include the 15 mirrored blocks); priority of the modulo-4 cut condition is unconfirmed. |

## Lean results

### 1. Exact fairness checker (`FiveDice.check30_iff`, [FiveDice.lean](FiveDice.lean))

Because only the relative order of the rolled faces matters, a labeling of five dice with $1, \ldots, 150$ is completely encoded by listing the **owner** of each label in increasing order using die indices $0, 1, 2, 3, 4$ (a length-150 sequence containing each index 30 times). A roll that produces the ascending ranking `[2, 0, 1, 4, 3]` (die 2 rolled lowest, then die 0, then 1, then 4, then 3 highest) corresponds precisely to choosing one occurrence of `2`, then `0`, then `1`, then `4`, then `3` from left to right in that owner sequence. Lean's kernel proves that the checker accepts a labeling if and only if each of the 120 rankings occurs exactly 202,500 times.

### 2. Necessary modulo-4 condition (`FiveDice.EqualCuts.needs_distinct_residues`, [EqualCuts.lean](EqualCuts.lean))

Pick any face on a given die and count how many *higher* labels belong to each of the four rival dice. One might hope for a highly uniform labeling where those four rival counts are always congruent modulo 4 at every face of a die. Lean proves in the kernel that this is impossible: in any permutation-fair labeling of five 30-sided dice, **every** die must have at least one face where two opponents' higher-label counts are not congruent modulo 4.

### 3. Mirrored permutation blocks ruled out (`FiveDice.Mirrored.no_fifteen_mirrored`, [MirroredObstruction.lean](MirroredObstruction.lean))

A natural symmetry ansatz builds the 150-label owner sequence from 15 consecutive 10-label blocks, where each block is a permutation of the 5 dice immediately followed by its reverse (for example, `[0, 1, 2, 3, 4, 4, 3, 2, 1, 0]`, which automatically balances the mean of every die). Using `native_decide` to verify 5,400 finite inequalities, Lean proves that no choice of 15 mirrored blocks can yield a fair labeling. (This is a special case of the Go First Dice team's earlier exclusion of all column-grouped labelings.)

### 4. Kernel-verified 60-sided example (`FiveDice.meyer60_fair`, [Meyer60.lean](Meyer60.lean))

Lean's kernel directly verifies Paul Meyer's five 60-sided Go First Dice, confirming that all 120 strict rankings occur exactly $60^5 / 120 = 6{,}480{,}000$ times.

## Verification and trust boundary

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

- **Pure Lean kernel:** `FiveDice.check30_iff`, `FiveDice.EqualCuts.needs_distinct_residues`, and `FiveDice.meyer60_fair`.
- **`native_decide` (trusts Lean's compiler and runtime):** `FiveDice.Mirrored.no_fifteen_mirrored` (5,400 finite inequalities).

## References

- Go First Dice: [Open Questions (`#d30`)](http://gofirstdice.ericharshbarger.org/doku.php?id=open_questions#d30) and [column-paired search counts](http://gofirstdice.ericharshbarger.org/doku.php?id=homogeneous_solutions#column_paired)
- [Gavenčiak, Haeupler, and Rozhoň, `arXiv:2610.15421v1`, §1.2](https://arxiv.org/html/2610.15421v1#S1.SS2)
- [The Dice Lab: Paul Meyer's 5 d60 Go First Dice](https://www.mathartfun.com/thedicelab.com/GFD5.html)
