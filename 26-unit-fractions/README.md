# Reciprocal Rado number f₂(26) = 2028 — a Lean 4 proof

**Prior-art status (22 November 2026):** no earlier proof of this exact
26-summand threshold was located. The lower bound and initial forcing
identities are published ingredients, credited below; earlier Lean work
also covers smaller reciprocal Rado numbers. The candidate contribution is
the upper bound at 26. See the [dated audit](../PRIOR_ART.md#reciprocal-rado).
This is a two-color unit-fraction Ramsey problem with repeated denominators.

**2028 is the smallest endpoint that guarantees a solution.** Color each integer from 1 to 2028 red or blue. You can always find 27 denominators of the same color such that

$$
\frac{1}{x_1}+\cdots+\frac{1}{x_{26}}=\frac{1}{y}.
$$

The denominators may repeat. This proves $f_2(26)=2028=3\cdot26^2$, the 26-summand case of Gaiser and Ramezanpour’s Conjecture 1.3. Their July 2026 paper gives the lower bound, tabulates exact values through $k=25$, and proves equality for $k=3\cdot2^m$ with $m\ge1$. Since 26 lies outside that family, the step needed here is the matching upper bound $f_2(26)\le2028$. [Conjecture 1.3](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem3) · [Theorem 1.2](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem2) · [Tables 1 and 2](https://arxiv.org/html/2607.04373v1#S3.T1)

## Why 2027 is too small

Color **3 through 77 red** and everything else blue. If all 26 summand denominators are at most $M$, their sum is at least $26/M$. To equal $1/y$, we must therefore have $26y\le M$.

- **Red.** Take $M=77$. Then $y\le 2$, and both 1 and 2 are blue.
- **Blue.** Take $M=2027$. Then $y\le 77$, so a blue target can only be $1$ or $1/2$. The terms with denominator 1 or 2 add up to a multiple of $1/2$. The remaining terms must also add up to a multiple of $1/2$, yet their sum is at most $26/78=1/3$. It must be zero. That leaves 26 terms of at least $1/2$ each, far too many for either target.

This is the paper’s lower-bound coloring specialized to 26 summands. [Theorem 1.1](https://arxiv.org/html/2607.04373v1#S2) · [Lean proof](UnitFractions/Lower.lean)

## Why 2028 is enough

Suppose a coloring avoids every solution. **Then $d$ and $26d$ have opposite colors** for each positive $d$ with $26d\le 2028$, because 26 copies of $1/(26d)$ add up to $1/d$. Below, $m/d$ stands for $m$ copies of $1/d$.

Call the color of 3 red. Then 78 is blue and 2028 is red. If 2 were blue, 52 would be red. The first identity below would force 39 red, making the second identity entirely red. So **2 and 3 are both red**, and 1352 is red as well.

$$
\frac12=\frac{13}{39}+\frac{13}{78},
\qquad
\frac13=\frac{12}{39}+\frac1{52}+\frac{13}{2028}.
$$

These two identities are the $k=26$ specialization of Case 1 in Gaiser and Ramezanpour’s proof of Theorem 3.3. [Theorem 3.3 and proof](https://arxiv.org/html/2607.04373v1#S3.Thmtheorem3)

The next four identities finish the argument at 26. Read them from top to bottom. In each row, the numerators on the right add up to 26.

| Identity | What follows |
| --- | --- |
| $1/2 = 1/3 + 2/13 + 6/1352 + 17/2028$ | 13 must be blue, so 338 is red. |
| $1/2 = 1/3 + 16/104 + 3/338 + 4/1352 + 2/2028$ | 104 must be blue, so 4 is red. |
| $1/2 = 1/3 + 1/8 + 12/338 + 1/1352 + 11/2028$ | 8 must be blue, so 208 is red. |
| $1/3 = 1/4 + 16/208 + 8/1352 + 1/2028$ | Every denominator is red. |

The last row gives the required contradiction. All six identities can be checked by multiplying by 8112. [Lean proof](UnitFractions/Upper.lean)

## Check the proof

Run `lake build` with Lean 4.36.0. The project uses only the standard library. The main theorem is `UnitFractions.forces_iff (N : Nat) : Forces N ↔ 2028 ≤ N`. [Theorem](UnitFractions.lean) · [Definition of a solution](UnitFractions/Basic.lean)
