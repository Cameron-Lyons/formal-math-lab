# OEIS A401159: counting $n \times 3$ binary matrices with at most two ones per row and column

Imagine filling an $n \times 3$ grid with $0$s and $1$s (a labeled `(0, 1)`-matrix). How many such grids have **at most two $1$s in every row** and **at most two $1$s in every column**? For every $n \ge 0$, the exact answer is

$$
H^3 - n^4 + \binom{n}{2}, \qquad \text{where } H = 1 + n + \binom{n}{2}.
$$

*(Quick sanity check: for $n = 1$, $H = 2$ gives $2^3 - 1^4 + 0 = 7$, matching all $8$ binary rows except `(1, 1, 1)`. For $n = 2$, $H = 4$ gives $4^3 - 2^4 + 1 = 49 = 7^2$, since the column bound is automatic on $2$ rows and each row independently has $7$ valid patterns.)*

This proves in Lean 4 the degree-6 polynomial conjectured by R. J. Mathar on 18 November 2026 in [OEIS A401159](https://oeis.org/A401159). The identity also follows from Adler and Ross's 2001 inclusion-exclusion formula for random subset coverings.

| Field | Summary |
| --- | --- |
| Problem | OEIS A401159, R. J. Mathar conjecture for labeled $n \times 3$ `(0, 1)`-matrices with row and column sums $\le 2$ |
| Status | Proved in Lean 4 for all $n \ge 0$ (also follows from Adler and Ross 2001). |
| Main theorems | `ThreeColumnMatrices.card_validMatrices`, `ThreeColumnMatrices.mathar_polynomial`, `ThreeColumnMatrices.count_correct` in [ThreeColumnMatrices.lean](ThreeColumnMatrices.lean) |
| Verification | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib v4.36.0; pure kernel proof) |
| Prior art | Checked 22 November 2026: confirms Mathar's conjecture in OEIS A401159; implied by Adler and Ross (2001), Corollary 1, eq. (6); no earlier Lean formalization was found. |

## How the proof works

**The big idea:** Because each row has only $3$ entries, requiring "at most two $1$s per row" is identical to forbidding **all-ones rows** `(1, 1, 1)`. So we first count all matrices that obey the column bound independently, and then use **inclusion-exclusion** to remove matrices containing one or more all-ones rows.

1. **Count column-valid matrices ($H^3$):** Each of the $3$ columns independently chooses $0$, $1$, or $2$ row positions for its $1$s, giving $H = 1 + n + \binom{n}{2}$ valid columns and $H^3$ matrices meeting the column bound.
2. **Subtract matrices with one specified all-ones row ($-n^4$):** Pick which row is all-ones ($n$ choices). Each column spends one of its $1$s in that row and can place at most one $1$ among the other $n - 1$ rows, leaving $1 + (n - 1) = n$ choices per column — hence $n^3$ matrices for that row, and $n \cdot n^3 = n^4$ across all $n$ rows.
3. **Add back matrices with two specified all-ones rows ($+\binom{n}{2}$):** Any matrix with two all-ones rows was subtracted twice in Step 2. Choose the pair of rows ($\binom{n}{2}$ choices); every column has now used both of its allowed $1$s, forcing all remaining entries to be $0$ and fixing the entire matrix.
4. **Stop — three or more all-ones rows are impossible:** Since each column holds at most two $1$s, no matrix can have three all-ones rows, so inclusion-exclusion terminates cleanly at $H^3 - n^4 + \binom{n}{2}$.

## Reproduce

Run from this directory with Lean and mathlib pinned to v4.36.0:

```sh
lake exe cache get
lake build
```

In namespace `ThreeColumnMatrices` ([ThreeColumnMatrices.lean](ThreeColumnMatrices.lean)):

* `card_validMatrices` proves the exact count $H^3 - n^4 + \binom{n}{2}$.
* `mathar_polynomial` proves this equals Mathar's expanded degree-6 polynomial.
* `count_correct` checks the executable counting function `count`.

## References

* [OEIS A401159](https://oeis.org/A401159) and [Mathar (2014), §2 and Table 2](https://oeis.org/A247158/a247158.pdf#page=2)
* [Adler and Ross (2001), Corollary 1, equation (6)](https://adler.ieor.berkeley.edu/ilans_pubs/coupons_2001.pdf#page=2)
