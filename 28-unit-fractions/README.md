# The reciprocal Rado number $f_2(28) = 2352$

Color every integer in $\{1, \ldots, N\}$ either red or blue. What is the smallest $N$ that guarantees a single-color solution (repetitions allowed) to the $28$-term unit-fraction equation

$$
\frac{1}{x_1} + \frac{1}{x_2} + \cdots + \frac{1}{x_{28}} = \frac{1}{y}?
$$

In Ramsey theory, this exact threshold is the two-color **reciprocal Rado number** $f_2(28)$. Here we prove in Lean 4 that $f_2(28) = 2352 = 3 \cdot 28^2$: every red-blue coloring of $\{1, \ldots, N\}$ has a monochromatic solution (all $29$ denominators the same color) if and only if $N \ge 2352$. This settles the $k = 28$ case of [Gaiser and Ramezanpour’s Conjecture 1.3](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem3).

| Field | Summary |
| --- | --- |
| Problem | Reciprocal Rado number $f_2(28) = 2352$ for $1/x_1 + \cdots + 1/x_{28} = 1/y$ (2 colors, repeated denominators allowed), Gaiser and Ramezanpour Conjecture 1.3 at $k = 28$ |
| Status | Case $k = 28$ proved in Lean 4 ($f_2(28) = 2352$). |
| Main theorem | `UnitFractions28.forces_iff (N : Nat) : Forces N ↔ 2352 ≤ N` in [UnitFractions.lean](UnitFractions.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof) |

## How the proof works

### Upper bound ($f_2(28) \le 2352$): clearing denominators once and for all

**The big idea:** Rather than juggling unit fractions $1/x_i$, we clear denominators once at the start using the common multiple $4704 = 2 \cdot 2352$. For every divisor $t$ of $4704$ with $2 \le t \le 2352$, its reciprocal partner $4704 / t$ also lies in $\{2, \ldots, 2352\}$. Color each such divisor $t$ by the color of $4704 / t$.

Under this re-indexing, any ordinary monochromatic sum of $28$ integers $t_1 + \cdots + t_{28} = s$ divides through by $4704$ to give a monochromatic unit-fraction solution:

$$
\frac{1}{4704/t_1} + \cdots + \frac{1}{4704/t_{28}} = \frac{1}{4704/s}.
$$

In particular, because $t + \cdots + t = 28t$ ($28$ copies), any avoiding coloring obeys the **opposites rule**: $t$ and $28t$ must have opposite colors whenever both lie in our divisor set. Stepping twice by $28$ therefore preserves color, so $t$ and $28^2 t = 784t$ always have the **same** color.

**Step 1: Force $2$ and $3$ to match.** By symmetry, call $2$ **red**. Stepping twice makes $1568 = 28^2 \cdot 2$ **red** as well. Now suppose $3$ were blue; then $84 = 28 \cdot 3$ would be red.

* The $28$-term sum $84 = 14(2 + 4)$ (i.e., $14$ copies of $2$ and $14$ copies of $4$) already has $84$ and $2$ red, forcing $4$ **blue** and hence $112 = 28 \cdot 4$ **red**.
* But then $1568 = 13 \cdot 112 + 84 + 14 \cdot 2$ ($13 + 1 + 14 = 28$ terms) is an all-red sum — a contradiction.

Thus $3$ must be **red**, and stepping twice makes $2352 = 28^2 \cdot 3$ **red** too. (This opening pair of identities adapts [Case 1 of Gaiser and Ramezanpour’s Theorem 3.3](https://arxiv.org/html/2607.04373v1#S3.Thmtheorem3).)

**Step 2: Three dominoes to contradiction.** Read the next three $28$-term sums in order. In each row, every number except the boxed one is already red, so the boxed number must be blue; dividing it by $28$ immediately yields a new red number for the next row.

| Sum of 28 terms | Next red number |
| --- | --- |
| $1568 = 9 \cdot \boxed{168} + 18 \cdot 3 + 2$ | $168 / 28 = 6$ |
| $2352 = 1568 + \boxed{672} + 15 \cdot 6 + 11 \cdot 2$ | $672 / 28 = 24$ |
| $1568 = \boxed{1176} + 13(24 + 6) + 2$ | $1176 / 28 = 42$ |

Now $2, 24, 42, 1568, 2352$ are all red, making every term and the target in the following $28$-term sum monochromatic red:

$$
2352 = 1568 + 10 \cdot 42 + 15 \cdot 24 + 2 \cdot 2.
$$

### Lower bound ($f_2(28) \ge 2352$): an avoiding coloring

To show $2351$ is insufficient, color $\{1, \ldots, 2351\}$ by painting $\{3, \ldots, 83\}$ **red** and $\{1, 2\} \cup \{84, \ldots, 2351\}$ **blue**.

Any solution satisfies $1/y = \sum_{i=1}^{28} 1/x_i \ge 28 / \max_i x_i$, so $28y \le \max_i x_i$.

* **No red solution:** Since $\max_i x_i \le 83$, we get $28y \le 83$, forcing $y \le 2$ — both blue.
* **No blue solution:** Since $\max_i x_i \le 2351$, we get $28y \le 2351$, so $y \le 83$, leaving only $y \in \{1, 2\}$ among blue integers. Terms with denominator $1$ or $2$ sum to a multiple of $1/2$, so the contribution from blue denominators $\ge 84$ must also be a multiple of $1/2$. Yet those terms total at most $28 / 84 = 1/3 < 1/2$, forcing that contribution to be zero. That leaves $28$ terms each at least $1/2$, whose sum is at least $14 > 1 \ge 1/y$.

This is the coloring from [Gaiser and Ramezanpour’s Theorem 1.1](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem1).

## Verification

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

Lean checks the six sums and the avoiding coloring and combines them in `UnitFractions28.forces_iff (N : Nat) : Forces N ↔ 2352 ≤ N`.

[Exact threshold](UnitFractions.lean) · [Upper bound](UnitFractions/Upper.lean) · [Lower bound](UnitFractions/Lower.lean)
