# Binary matrices with three columns

For every integer $n\ge 0$, the number of labeled $n\times 3$ binary matrices with
at most two ones in each row and column is

$$
H^3-n^4+\binom{n}{2}, \qquad H=1+n+\binom{n}{2}.
$$

Each column has $H$ choices. A specified all-ones row leaves $n$ choices per
column, so subtract $n\cdot n^3$. Two specified all-ones rows determine the
whole matrix, so add back $\binom{n}{2}$. Three all-ones rows are impossible.

Run `lake build` in this directory with Lean 4.36.0 and the pinned mathlib
dependency. In the `ThreeColumnMatrices` namespace, `card_validMatrices` proves
the count, `mathar_polynomial` gives its degree-six expansion, and
`count_correct` verifies the executable function `count`. [Lean source](ThreeColumnMatrices.lean)

Mathar stated the polynomial as a conjecture in OEIS A401159. The identity also
follows from earlier subset-counting results. [OEIS A401159](https://oeis.org/A401159) ·
[Prior-art audit](../PRIOR_ART.md#three-column-matrices)
