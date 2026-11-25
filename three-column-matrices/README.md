# OEIS A401159: Counting n x 3 binary matrices with at most two ones per row and column — Lean 4 proof

**Exact formula proved in Lean 4 for all $n \ge 0$.** The number of labeled $n \times 3$ binary `(0, 1)`-matrices with at most two ones in every row and at most two ones in every column is

$$
H^3 - n^4 + \binom{n}{2}, \qquad \text{where } H = 1 + n + \binom{n}{2}.
$$

This proves the degree-6 polynomial stated as a conjecture by R. J. Mathar on 18 November 2026 in [OEIS A401159](https://oeis.org/A401159). (The identity also follows from Adler and Ross's 2001 inclusion–exclusion formula for random subset coverings.)

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **OEIS A401159** (`A401159`), R. J. Mathar conjecture: count of labeled `n x 3` binary `(0, 1)`-matrices with row sums $\le 2$ and column sums $\le 2$, formula `(1 + n + C(n,2))^3 - n^4 + C(n,2)` |
| **Status** | **Completely proved in Lean 4 for all $n \ge 0$** (also follows from Adler–Ross 2001). |
| **Main Lean theorems** | `ThreeColumnMatrices.card_validMatrices`, `ThreeColumnMatrices.mathar_polynomial`, `ThreeColumnMatrices.count_correct` in [ThreeColumnMatrices.lean](ThreeColumnMatrices.lean) |
| **Verification** | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib v4.36.0; pure kernel proof) |
| **Prior-art status** | Checked **22 November 2026**: confirms Mathar's conjecture in OEIS A401159; mathematically implied by Adler–Ross (2001), Corollary 1, eq. (6); no earlier Lean formalization located. See [PRIOR_ART.md](../PRIOR_ART.md#three-column-matrices). |

## Proof overview

Each column independently has at most two ones among $n$ rows, giving $H = 1 + n + \binom{n}{2}$ choices per column and $H^3$ matrices meeting the column bound. Exclude matrices containing an all-ones row by inclusion–exclusion:

* **One specified all-ones row ($n$ choices):** each column has 1 one fixed in that row and at most 1 one among the remaining $n - 1$ rows, leaving $1 + (n - 1) = n$ choices per column, so subtract $n \cdot n^3 = n^4$.
* **Two specified all-ones rows ($\binom{n}{2}$ choices):** every column has already used its maximum of two ones, uniquely determining the whole matrix, so add back $\binom{n}{2}$.
* **Three or more all-ones rows:** impossible since each column has at most two ones.

## Reproduce

Run from this directory with Lean and mathlib pinned to **v4.36.0**:

```sh
lake exe cache get
lake build
```

In namespace `ThreeColumnMatrices` ([ThreeColumnMatrices.lean](ThreeColumnMatrices.lean)):

* `card_validMatrices` proves the exact cardinality $H^3 - n^4 + \binom{n}{2}$.
* `mathar_polynomial` proves equality with Mathar's expanded degree-6 polynomial.
* `count_correct` verifies the executable counting function `count`.

## References

* [OEIS A401159](https://oeis.org/A401159) · [Mathar (2014), §2 and Table 2](https://oeis.org/A247158/a247158.pdf#page=2)
* [Adler and Ross (2001), Corollary 1, equation (6)](https://adler.ieor.berkeley.edu/ilans_pubs/coupons_2001.pdf#page=2)
* [Dated prior-art audit](../PRIOR_ART.md#three-column-matrices)
