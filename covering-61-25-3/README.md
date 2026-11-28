# Covering design $C(61, 25, 3)$

Imagine selecting 25-element subsets (**blocks**) from a 61-element ground set so that *every* 3-element subset (all $\binom{61}{3} = 35{,}990$ triples) is contained inside at least one block. Such a family is called a **$(61, 25, 3)$ covering design**, and the minimum number of blocks required is denoted $C(61, 25, 3)$.

Caleb Ashton published an explicit 27-block covering design, establishing $C(61, 25, 3) \le 27$, while standard lower bounds force at least 26 blocks. Whether $C(61, 25, 3)$ equals 26 or 27 remains open. The Lean 4 proofs here establish strong local-repair obstructions: **no** 26-block cover can keep 21 or more of the 27 published blocks (checked exhaustively across all $\binom{27}{21} = 296{,}010$ subsets via `Covering61.RepairSearch.published_six_for_five_screen`). We also verify a near-miss 26-block candidate that misses only 84 of the 35,990 triples and prove that neither 2-block nor 3-block replacements can repair it.

| Field | Summary |
| --- | --- |
| Problem | Covering design $C(61, 25, 3)$ ($26 \le C(61, 25, 3) \le 27$), Caleb Ashton's 27-block construction (`covering-C61-25-3-27`) |
| Status | Partial result (local-repair obstructions). Any 26-block cover keeps at most 20 of the 27 published blocks; unrestricted existence of a 26-block cover remains open. |
| Main theorems | `Covering61.RepairSearch.published_six_for_five_screen` (plus `published_five_for_four_screen`, `published_four_for_three_screen`, `candidate_three_group_screen`) in [RepairSearch.lean](RepairSearch.lean); two-replacement proofs in [Repairs.lean](Repairs.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; `native_decide` for the 296,010-case screen); independent C++ checker in [SixGroupSearch.cpp](SixGroupSearch.cpp) |
| Prior art | Checked 23-24 November 2026: Caleb Ashton published the 27-block construction; unrestricted existence of a 26-block cover remains open. See [PRIOR_ART.md](../PRIOR_ART.md). |

## What is proved

### 1. Any 26-block cover keeps at most 20 of the 27 published blocks

Suppose a 26-block cover kept 21 of the 27 published blocks. Dropping the other 6 published blocks leaves some set of uncovered triples, and we have only 5 new replacement blocks to cover all of them. Think of each 25-element block as having 25 **seats** for elements: the 5 replacement blocks provide $5 \times 25 = 125$ seats in total, and placing an element $m$ times across those 5 blocks uses up $m$ seats.

Across all $\binom{27}{6} = 296{,}010$ ways to drop 6 published blocks and try to replace them with 5, a two-stage counting screen eliminates every case:

1. **Stage 1 — Seat and pair-meeting lower bounds ($296{,}010 \to 1{,}388$ survivors):**
   - *Pair co-occurrence bound:* Whenever a pair of points $\{x, y\}$ appears together in a 25-element block, only $25 - 2 = 23$ seats remain in that block for third elements. Hence if $\{x, y\}$ still needs to meet $d$ different third elements in missing triples, $\{x, y\}$ must appear together in at least $\lceil d / 23 \rceil$ of the 5 blocks.
   - *Degree-to-seat bound:* Each single appearance of a point in a 25-element block shares that block with 24 other points, so it covers at most 24 pair meetings.
   - *Pigeonhole overlap:* Two points appearing $s$ and $t$ times among 5 blocks must co-occur in at least $s + t - 5$ blocks.
   - *Two-appearance incompatibility:* If a point appears in only two of the 5 blocks, two companions that each appear in only one of its two opposite blocks can never join it in a common block, so they cannot form a missing triple with it.

   Applying these bounds rules out all but **1,388** of the 296,010 choices.

2. **Stage 2 — Forced single-appearance sets ($1{,}388 \to 0$ survivors):**
   - If a point appears only *once* among the 5 blocks, every partner it needs in a missing triple must fit into that same block, and any two such single-appearance points sharing a missing triple are forced into the same block.
   - Every extra appearance of a point beyond its minimum uses up one of the few spare seats out of 125, letting us enumerate which points may appear more than once and test every placement of the forced sets into the 5 blocks.
   - For each candidate placement, we recount seats—forcing pairs inside a forced block to meet again whenever their required third elements do not all fit there, and crossing off completed 25-element blocks.

   **None** of the 1,388 remaining choices survive. (The same screen also proves the smaller local exclusions `published_five_for_four_screen` and `published_four_for_three_screen`.)

### 2. The 26-block candidate missing 84 triples

[Covering.lean](Covering.lean) verifies an explicit 26-block candidate that covers 35,906 of the 35,990 triples (missing only 84). [Repairs.lean](Repairs.lean) proves directly in Lean that any 2-block replacement of this candidate requires at least 52 seats, whereas 2 blocks supply only $2 \times 25 = 50$ seats. Finally, `candidate_three_group_screen` rules out every 3-block replacement under the same counting screen.

## Verification and trust boundary

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

- **Lean files:**
  - [RepairSearch.lean](RepairSearch.lean): proves that the surviving-case list is empty using `native_decide` (which trusts Lean's compiler and runtime for the 296,010-case finite evaluation).
  - [RepairCount.lean](RepairCount.lean): implementation and soundness of the counting and forced-set screen.
  - [Repairs.lean](Repairs.lean): direct two-replacement proofs for the 84-triple candidate.
  - [Covering.lean](Covering.lean): the published 27-block cover and the 26-block near-miss candidate.
- **Independent C++23 check:** An independent external C++23 program reproduces the intermediate surviving counts directly from `Covering.lean`:

```sh
c++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror SixGroupSearch.cpp -o six-group-search
./six-group-search Covering.lean
```

## References

- [Caleb Ashton's published 27-block covering design `C(61, 25, 3) <= 27`](https://kaust-a-laut.github.io/results/covering-C61-25-3-27/README.md)
- [SixGroupSearch.cpp](SixGroupSearch.cpp)
- [Prior-art audit](../PRIOR_ART.md)
