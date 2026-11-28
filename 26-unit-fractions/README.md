# Reciprocal Rado number $f_2(26) = 2028$

Paint every integer from $1$ to $N$ either red or blue. How large must $N$ be to guarantee that you can pick $27$ numbers of the **same color** (repeats allowed) whose reciprocals satisfy

$$
\frac{1}{x_1} + \frac{1}{x_2} + \cdots + \frac{1}{x_{26}} = \frac{1}{y}?
$$

In Ramsey theory, this exact threshold is called the two-color **reciprocal Rado number** $f_2(26)$. Here we prove in Lean 4 that $f_2(26) = 2028 = 3 \cdot 26^2$: every red-blue coloring of $\{1, \ldots, 2028\}$ forces a monochromatic solution, whereas $\{1, \ldots, 2027\}$ can be colored to avoid one.

This settles the $k = 26$ case of Gaiser and Ramezanpour's Conjecture 1.3 (`arXiv:2607.04373`), which asks whether $f_2(k) = 3k^2$ for all $k$. Their July 2026 paper establishes the general lower bound, lists exact values through $k = 25$, and proves equality for $k = 3 \cdot 2^m$, leaving $k = 26$ as the first open case.

| Field | Summary |
| --- | --- |
| Problem | Reciprocal Rado number $f_2(26) = 2028$ for $1/x_1 + \cdots + 1/x_{26} = 1/y$ (2 colors, repeated denominators allowed), Gaiser and Ramezanpour (`arXiv:2607.04373v1`) Conjecture 1.3 at $k = 26$ |
| Status | Case $k = 26$ proved in Lean 4 ($f_2(26) = 2028$). The general conjecture $f_2(k) = 3k^2$ remains open. |
| Main theorem | `UnitFractions.forces_iff (N : Nat) : Forces N ↔ 2028 ≤ N` in [UnitFractions.lean](UnitFractions.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof) |
| Prior art | Checked 22 November 2026: no earlier proof of the 26-summand upper bound was found. The lower-bound coloring and initial forcing identities come from Gaiser and Ramezanpour, and earlier Lean projects cover smaller $k$. See [PRIOR_ART.md](../PRIOR_ART.md#reciprocal-rado). |

## How the proof works

### Lower bound ($f_2(26) \ge 2028$): an avoiding coloring

To show that $N = 2027$ is too small, we paint $\{1, \ldots, 2027\}$ in two bands:

* **Red:** the middle band $\{3, 4, \ldots, 77\}$.
* **Blue:** the remaining integers $\{1, 2\} \cup \{78, 79, \ldots, 2027\}$.

First observe a basic size constraint: if all $26$ summand denominators $x_i$ are at most $M$, then each term $1/x_i$ is at least $1/M$. Their sum $1/y$ is therefore at least $26 / M$, which forces $26 y \le M$.

* **No red solution:** Here $M = 77$, so $26y \le 77$, which forces $y \le 2$. Neither $1$ nor $2$ is red.
* **No blue solution:** Here $M = 2027$, so $26y \le 2027$, giving $y \le 77$. Because $\{3, \ldots, 77\}$ are all red, a blue target must be $y = 1$ or $y = 2$. Any summands with denominator $1$ or $2$ add up to an integer multiple of $1/2$, while all remaining blue denominators are at least $78$ and together contribute at most $26 / 78 = 1/3 < 1/2$. For the grand total $1/y \in \{1, 1/2\}$ to be a multiple of $1/2$, **none** of those large denominators can appear. That leaves $26$ summands each at least $1/2$ — summing to at least $13$, far larger than both $1$ and $1/2$.

This specializes Gaiser and Ramezanpour's lower-bound coloring to $k = 26$ ([Theorem 1.1](https://arxiv.org/html/2607.04373v1#S2), [UnitFractions/Lower.lean](UnitFractions/Lower.lean)).

### Upper bound ($f_2(26) \le 2028$): the opposites trick and a six-step domino chain

Suppose for contradiction that some red-blue coloring of $\{1, \ldots, 2028\}$ avoids monochromatic solutions.

**The big idea (the opposites trick):** Because $26$ copies of $1/(26d)$ sum to $1/d$, the integers $d$ and $26d$ **must have opposite colors** whenever $d \ge 1$ and $26d \le 2028$. Applying this rule twice tells us that $d$ and $26^2 d = 676d$ always have the **same** color.

Throughout the identities below, $m/d$ is shorthand for $m$ copies of the unit fraction $1/d$.

**Step 1: Force $2$ and $3$ to share a color.** By color symmetry, call $3$ **red**. By the opposites trick, $26 \cdot 3 = 78$ is **blue** and $26 \cdot 78 = 2028$ is **red**. Could $2$ be blue? If $2$ were blue, then $26 \cdot 2 = 52$ would be red. Look at the two $26$-term identities

$$
\frac{1}{2} = \frac{13}{39} + \frac{13}{78},
\qquad
\frac{1}{3} = \frac{12}{39} + \frac{1}{52} + \frac{13}{2028}.
$$

In the first identity, $2$ and $78$ are both blue, so $39$ must be red to avoid an all-blue solution. But then $3, 39, 52, 2028$ are all red, making the second identity monochromatic red — a contradiction. Thus $2$ must be **red** too, which immediately forces $52$ **blue** and $26 \cdot 52 = 1352$ **red**.

(These two identities specialize Case 1 of Gaiser and Ramezanpour's proof of [Theorem 3.3](https://arxiv.org/html/2607.04373v1#S3.Thmtheorem3) to $k = 26$.)

**Step 2: Four dominoes to contradiction.** We now know that $2, 3, 1352, 2028$ are all red. Read the four identities below in order: in each of the first three rows, every denominator *except one* is already red, forcing that remaining denominator to be blue — and multiplying or dividing it by $26$ yields a fresh red number for the next row. The fourth row then has every denominator red.

In every row, the right-hand numerators add up to $26$, and multiplying by $8112$ clears all denominators across all six identities:

| Identity | Forced color |
| --- | --- |
| $1/2 = 1/3 + 2/13 + 6/1352 + 17/2028$ | $13$ must be blue, so $26 \cdot 13 = 338$ is red. |
| $1/2 = 1/3 + 16/104 + 3/338 + 4/1352 + 2/2028$ | $104$ must be blue, so $104 / 26 = 4$ is red. |
| $1/2 = 1/3 + 1/8 + 12/338 + 1/1352 + 11/2028$ | $8$ must be blue, so $26 \cdot 8 = 208$ is red. |
| $1/3 = 1/4 + 16/208 + 8/1352 + 1/2028$ | Every denominator is red — contradiction. |

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
