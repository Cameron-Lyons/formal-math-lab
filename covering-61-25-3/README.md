# Covering design C(61, 25, 3): 26-block repair obstructions and 84-triple candidate check — Lean 4 proofs

**Status: whether the covering number $C(61, 25, 3)$ equals 26 or 27 remains open.** A $(61, 25, 3)$ covering design is a collection of 25-element subsets (*blocks* / *groups*) of a 61-element set such that every 3-element subset (all $\binom{61}{3} = 35{,}990$ triples) is contained in at least one block. Caleb Ashton published a 27-block covering ($C(61, 25, 3) \le 27$).

This Lean 4 project proves that **no 26-block $(61, 25, 3)$ covering design can retain more than 20 of the 27 published blocks** (exhausting all $\binom{27}{21} = 296{,}010$ choices of 21 retained blocks via `Covering61.RepairSearch.published_six_for_five_screen`), and verifies a 26-block candidate that misses only 84 of the 35,990 triples (proving no 2-block replacement can repair it).

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Covering design `C(61, 25, 3)`** (`v = 61, k = 25, t = 3`), covering number $26 \le C(61, 25, 3) \le 27$, Caleb Ashton's 27-block construction (`covering-C61-25-3-27`) |
| **Status** | **Partial result (local-repair obstructions).** Any 26-block cover can keep at most 20 of the 27 published blocks; existence of an unrestricted 26-block cover remains open. |
| **Main Lean theorems** | `Covering61.RepairSearch.published_six_for_five_screen` (plus `published_five_for_four_screen`, `published_four_for_three_screen`, `candidate_three_group_screen`) in [RepairSearch.lean](RepairSearch.lean); two-replacement proofs in [Repairs.lean](Repairs.lean) |
| **Verification** | `lake build` (Lean 4.36.0, stdlib only; `native_decide` for the 296,010-case screen); independent C++ checker in [SixGroupSearch.cpp](SixGroupSearch.cpp) |
| **Prior-art status** | Checked **23–24 November 2026**: Caleb Ashton published the 27-block construction; unrestricted existence of a 26-block cover remains open. See [PRIOR_ART.md](../PRIOR_ART.md). |

## What is proved

### Any 26-block cover retains at most 20 of the 27 published blocks

Suppose a 26-block covering retained 21 of the 27 published blocks. Its 5 replacement blocks have $5 \times 25 = 125$ total seats and must cover every triple missed by those 21 blocks. Across all $\binom{27}{6} = 296{,}010$ ways to drop 6 published blocks and replace them with 5, the following counting screen eliminates every single choice:

1. **Seat and pair-meeting lower bounds:** if a pair of elements still needs to meet $d$ different third elements, that pair must appear together in at least $\lceil d / 23 \rceil$ of the 5 blocks; each appearance of a point covers at most 24 pair meetings; two points appearing $s$ and $t$ times among 5 blocks must co-occur in at least $s + t - 5$ blocks; and for a point appearing twice, two companions exclusive to opposite blocks cannot form a missing triple with it. Applying these bounds leaves 1,388 of the 296,010 choices.
2. **Forced single-appearance sets:** for any point appearing only once among the 5 blocks, all of its partners in missing triples must fit into that single block, and two such points sharing a missing triple must share that block. Because every extra appearance consumes a spare seat, we can enumerate which points may appear more than once, try all placements of the forced sets into the 5 blocks, and recount seats (requiring pairs in a forced block to meet again if their missing third elements do not all fit there, and crossing off completed 25-sets). **Zero choices survive.**

### The 26-block candidate missing 84 triples

[Covering.lean](Covering.lean) checks an explicit 26-block candidate that covers 35,906 of the 35,990 triples (missing exactly 84 triples). [Repairs.lean](Repairs.lean) proves directly in Lean that any 2-block replacement of this candidate requires at least 52 seats (only 50 are available), and `candidate_three_group_screen` rules out 3-block replacements under the same counting screen.

## Reproduce the checks

Run from this directory with Lean **4.36.0** (standard library only):

```sh
lake build
```

* [RepairSearch.lean](RepairSearch.lean): main theorem verifying that the surviving-case list is empty (uses `native_decide`).
* [RepairCount.lean](RepairCount.lean): implementation of the counting and forced-set screen (completeness of the bounds is explained above and in the source).
* [Repairs.lean](Repairs.lean): direct two-replacement proofs for the 84-triple candidate.
* [Covering.lean](Covering.lean): published 27-block cover and 26-block candidate.

An independent C++20 program reproduces the intermediate surviving counts:

```sh
c++ -std=c++20 -O3 SixGroupSearch.cpp -o six-group-search
./six-group-search Covering.lean
```

## References

* [Caleb Ashton's published 27-block covering design `C(61, 25, 3) <= 27`](https://kaust-a-laut.github.io/results/covering-C61-25-3-27/README.md)
* [Independent C++ checker](SixGroupSearch.cpp)
* [Dated prior-art audit](../PRIOR_ART.md)
