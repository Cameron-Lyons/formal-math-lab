# Reciprocal Rado number f_2(26) = 2028

Color every integer in $\{1, 2, \ldots, N\}$ red or blue. Then $N = 2028 = 3 \cdot 26^2$ is the smallest bound that forces 27 monochromatic positive integers (repeated denominators allowed) satisfying

$$
\frac{1}{x_1} + \frac{1}{x_2} + \cdots + \frac{1}{x_{26}} = \frac{1}{y}.
$$

This settles the $k = 26$ case of Gaiser and Ramezanpour's Conjecture 1.3 (`arXiv:2607.04373`), which asks whether $f_2(k) = 3k^2$ for all $k$. Their July 2026 paper gives the lower bound, lists exact values through $k = 25$, and proves equality for $k = 3 \cdot 2^m$, leaving $k = 26$ as the first open case.

| Field | Summary |
| --- | --- |
| Problem | Reciprocal Rado number $f_2(26) = 2028$ for $1/x_1 + \cdots + 1/x_{26} = 1/y$ (2 colors, repeated denominators allowed), Gaiser and Ramezanpour (`arXiv:2607.04373v1`) Conjecture 1.3 at $k = 26$ |
| Status | Case $k = 26$ proved in Lean 4 ($f_2(26) = 2028$). The general conjecture $f_2(k) = 3k^2$ remains open. |
| Main theorem | `UnitFractions.forces_iff (N : Nat) : Forces N ↔ 2028 ≤ N` in [UnitFractions.lean](UnitFractions.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof) |
| Prior art | Checked 22 November 2026: no earlier proof of the 26-summand upper bound was found. The lower-bound coloring and initial forcing identities come from Gaiser and Ramezanpour, and earlier Lean projects cover smaller $k$. See [PRIOR_ART.md](../PRIOR_ART.md#reciprocal-rado). |

## Proof overview

### Lower bound ($f_2(26) \ge 2028$)

Color 3 through 77 red and all other integers in $\{1, \ldots, 2027\}$ blue. If all 26 summand denominators are at most $M$, their sum is at least $26 / M$, so equality with $1 / y$ requires $26 y \le M$.

* Red: take $M = 77$. Then $y \le 2$, and both 1 and 2 are blue.
* Blue: take $M = 2027$. Then $y \le 77$, so a blue target must be $y = 1$ or $y = 2$. Terms with denominator 1 or 2 sum to a multiple of $1/2$. The remaining blue denominators are at least 78, so they contribute at most $26 / 78 = 1/3$. For the total to be a multiple of $1/2$, none of those terms can appear. That leaves 26 terms each at least $1/2$, which is bigger than both $1$ and $1/2$.

This specializes Gaiser and Ramezanpour's lower-bound coloring to $k = 26$ ([Theorem 1.1](https://arxiv.org/html/2607.04373v1#S2), [UnitFractions/Lower.lean](UnitFractions/Lower.lean)).

### Upper bound ($f_2(26) \le 2028$)

Suppose a 2-coloring of $\{1, \ldots, 2028\}$ avoids monochromatic solutions. Then $d$ and $26d$ must have opposite colors whenever $d \ge 1$ and $26d \le 2028$, because 26 copies of $1/(26d)$ sum to $1/d$. Below, $m/d$ means $m$ copies of $1/d$.

Call the color of 3 red; then 78 is blue and 2028 is red. If 2 were blue, then 52 would be red. The first identity below would force 39 red, making the second identity all red. So 2 and 3 are both red, which makes 52 blue and $26 \cdot 52 = 1352$ red:

$$
\frac{1}{2} = \frac{13}{39} + \frac{13}{78},
\qquad
\frac{1}{3} = \frac{12}{39} + \frac{1}{52} + \frac{13}{2028}.
$$

These two identities specialize Case 1 of Gaiser and Ramezanpour's proof of [Theorem 3.3](https://arxiv.org/html/2607.04373v1#S3.Thmtheorem3) to $k = 26$.

Four more identities finish the contradiction at $k = 26$. In each row, the right-hand numerators sum to 26, and multiplying by 8112 clears all denominators in all six identities:

| Identity | Forced color |
| --- | --- |
| $1/2 = 1/3 + 2/13 + 6/1352 + 17/2028$ | 13 must be blue, so $26 \cdot 13 = 338$ is red. |
| $1/2 = 1/3 + 16/104 + 3/338 + 4/1352 + 2/2028$ | 104 must be blue, so $104 / 26 = 4$ is red. |
| $1/2 = 1/3 + 1/8 + 12/338 + 1/1352 + 11/2028$ | 8 must be blue, so $26 \cdot 8 = 208$ is red. |
| $1/3 = 1/4 + 16/208 + 8/1352 + 1/2028$ | Every denominator is red, contradiction. |

Lean proof: [UnitFractions/Upper.lean](UnitFractions/Upper.lean).

## Check the proof

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

The main theorem is `UnitFractions.forces_iff (N : Nat) : Forces N ↔ 2028 ≤ N` in [UnitFractions.lean](UnitFractions.lean), with the solution predicate in [UnitFractions/Basic.lean](UnitFractions/Basic.lean).

## References

* Gaiser and Ramezanpour, `arXiv:2607.04373v1`: [Conjecture 1.3](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem3), [Theorem 1.2](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem2), [Tables 1 and 2](https://arxiv.org/html/2607.04373v1#S3.T1)
* [Prior-art audit](../PRIOR_ART.md#reciprocal-rado)
