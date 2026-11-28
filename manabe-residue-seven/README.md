# Manabe's subtraction game $\{3, 8, 11k + 7\}$

Consider the impartial **subtraction game** with move set $S = \{3, 8, 11k + 7\}$ for any integer $k \ge 1$: from a heap of $n$ tokens, a player may remove $3$, $8$, or $11k + 7$ tokens whenever enough tokens remain, and the last player to move wins. Each heap size $n$ has a **Grundy value** (or *nim-value*) $g(n)$ — the smallest nonnegative integer missing from the Grundy values of the heaps reachable in one move (the **mex** rule). Because the move set is finite, the sequence $g(0), g(1), \ldots$ always becomes periodic eventually, after some initial non-repeating **preperiod**.

The Lean 4 proof here computes the exact Sprague-Grundy sequence for every $k \ge 1$. It proves that $g(n) = 3$ if and only if $n = 11k + 10$ (`SubtractionGame.grundy_eq_three_iff`), confirming the positive preperiod predicted in Manabe's Example 1 (`arXiv:2609.05358`, residue $7 \bmod 11$). Furthermore, the least preperiod is $11k + 11$ and the least eventual period is $11k + 10$.

| Field | Summary |
| --- | --- |
| Problem | Manabe's subtraction game with move set $\{3, 8, 11k + 7\}$ ($k \ge 1$), `arXiv:2609.05358v2` Example 1 (residue $7 \bmod 11$) |
| Status | Proved in Lean 4 for all $k \ge 1$. |
| Main theorems | `SubtractionGame.grundy_eq_three_iff`, `prefix_formula`, `tail_formula`, `tail_period`, `lower_bound_on_preperiod`, `not_purely_periodic` ([UniqueThree.lean](UniqueThree.lean)) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof) |
| Prior art | Checked 23 November 2026: no earlier proof of the singleton-3 statement for all $k \ge 1$ was found; REUF working notes anticipate the repeating block. |

## Exact Grundy sequence

Define three short building-block words:

* `A = 00011100211` (length $11$ — the repeating period of the two-move game $\{3, 8\}$)
* `B = 00011102213` (length $11$)
* `D = 0021100211` (length $10$)

Starting from heap $n = 0$, the complete Sprague-Grundy sequence for $\{3, 8, 11k + 7\}$ ($k \ge 1$) is

$$
A^k B\, (D A^k)^\infty.
$$

**Concrete example ($k = 1$, moves $\{3, 8, 18\}$):** The non-repeating prefix $AB = \texttt{00011100211}\,\texttt{00011102213}$ has length $22$ (heaps $0$ through $21$), putting the lone `3` at heap $21 = 11(1) + 10$. From heap $22 = 11(1) + 11$ onward, the $21$-digit block $DA = \texttt{0021100211}\,\texttt{00011100211}$ repeats forever.

In general, for every $k \ge 1$:

* The only `3` in the entire sequence is the last digit of `B`, at heap size $n = 11k + 10$.
* The sequence is not purely periodic (`not_purely_periodic`): its least preperiod is $11k + 11$ (`lower_bound_on_preperiod`) and its least eventual period is $11k + 10$ (`tail_period`).

## How the proof works

**The big idea (block alignment and window locking):** Why can a single finite check settle infinitely many values of $k$ and infinitely many heap sizes $n$?

1. **Three-row grid alignment:** Arrange the first $3(11k + 10)$ candidate values into three rows of width $q = 11(k + 1)$. Because the word `A` has length $11$, all interior copies of `A` align cleanly and see the exact same three-move neighborhood regardless of $k$.
2. **Reduction to $k = 2$:** Verifying the mex recurrence for every $k \ge 1$ therefore reduces to checking one interior block together with the boundary blocks — all of which already appear in the $k = 2$ case ($99$ entries, verified directly in [Window.lean](Window.lean)).
3. **Sliding-window periodicity lock:** The largest legal move is $11k + 7$, so every heap's Grundy value depends only on the preceding $11k + 7$ heaps. Once rows $1$ and $2$ agree across a window longer than $11k + 7$, induction forces the tail to repeat with period $11k + 10$ for all larger heaps forever. Because `3` appears at $n = 11k + 10$ and never again, no period can begin before $n = 11k + 11$.

## Reproduce

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

## References

* [Manabe, `arXiv:2609.05358v2`, Example 1](https://arxiv.org/html/2609.05358v2#S1)
* [REUF working notes (`AIM2024`)](https://github.com/ZacharyHenderson111/AIM2024/blob/main/CollectiveNotes/oldVerifiedCases/verifiedcases2023.tex#L374-L418)
* [UniqueThree.lean](UniqueThree.lean) and [Window.lean](Window.lean)
