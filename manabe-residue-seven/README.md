# Manabe's subtraction game {3, 8, 11k + 7} (arXiv:2609.05358 Example 1): exact Grundy sequence, preperiod, and unique value 3 — Lean 4 proof

**Solved for all $k \ge 1$ in Lean 4.** Consider the impartial subtraction game with move set $S = \{3, 8, 11k + 7\}$ for any integer $k \ge 1$: from a heap of $n$ tokens, a player may remove $3$, $8$, or $11k + 7$ tokens (whenever enough tokens remain).

This Lean 4 project proves the complete Sprague–Grundy (nim-value) sequence for every $k \ge 1$: **the Grundy value equals 3 if and only if $n = 11k + 10$** (`SubtractionGame.grundy_eq_three_iff`), proving the positive preperiod predicted in **Manabe's Example 1** (`arXiv:2609.05358`, residue $7 \bmod 11$). Specifically, the least preperiod is **$11k + 11$** and the least eventual period is **$11k + 10$**.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Manabe's subtraction game** with move set `{3, 8, 11k + 7}` ($k \ge 1$), `arXiv:2609.05358v2` Example 1 (residue $7 \bmod 11$), Sprague–Grundy / nim-value sequence, unique Grundy value 3 at `n = 11k + 10`, preperiod `11k + 11`, period `11k + 10` |
| **Status** | **Completely proved in Lean 4 for all $k \ge 1$.** |
| **Main Lean theorems** | `SubtractionGame.grundy_eq_three_iff`, `prefix_formula`, `tail_formula`, `tail_period`, `lower_bound_on_preperiod`, `not_purely_periodic` ([UniqueThree.lean](UniqueThree.lean)); `manabe_eq_three_iff` ([ManabeBridge.lean](ManabeBridge.lean)) |
| **Verification** | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof) |
| **Prior-art status** | Checked **23 November 2026**: no earlier proof of the singleton-3 statement for all $k \ge 1$ located; REUF working notes anticipate the repeating block. See [PRIOR_ART.md](../PRIOR_ART.md#manabes-subtraction-game). |

## Exact Grundy sequence

Define the three finite words:

* `A = 00011100211` (length 11)
* `B = 00011102213` (length 11)
* `D = 0021100211` (length 10)

Starting at heap $n = 0$, the Sprague–Grundy sequence for subtraction set $\{3, 8, 11k + 7\}$ ($k \ge 1$) is:

$$
A^k B\, (D A^k)^\infty.
$$

* The **only** occurrence of `3` is the final digit of `B`, at heap size $n = 11k + 10$.
* The sequence is not purely periodic (`not_purely_periodic`): its least preperiod is $11k + 11$ (`lower_bound_on_preperiod`) and its least eventual period is $11k + 10$ (`tail_period`).

### Proof idea

Writing the first $3(11k + 10)$ candidate values in three rows of width $q = 11(k + 1)$ reduces the mex recurrence for every $k \ge 1$ to checking a single interior block plus boundary blocks (handled by $k = 2$, 99 entries checked in [Window.lean](Window.lean)). Once rows 1 and 2 agree across a window longer than the largest move $11k + 7$, periodicity propagates to all larger heaps forever.

## Reproduce

Run from this directory with Lean **4.36.0** (standard library only):

```sh
lake build
```

An optional bridge file ([ManabeBridge.lean](ManabeBridge.lean)) includes commands to fetch Manabe's own Lean Grundy definition and verify `SubtractionGame.manabe_eq_three_iff` directly against it.

## References

* [Manabe, `arXiv:2609.05358v2`, Example 1](https://arxiv.org/html/2609.05358v2#S1)
* [REUF working notes (`AIM2024`)](https://github.com/ZacharyHenderson111/AIM2024/blob/main/CollectiveNotes/oldVerifiedCases/verifiedcases2023.tex#L374-L418)
* [Main Lean proofs](UniqueThree.lean) · [Window reduction](Window.lean) · [Dated prior-art audit](../PRIOR_ART.md#manabes-subtraction-game)
