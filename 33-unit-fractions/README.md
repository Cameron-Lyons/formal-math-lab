# The 33-term reciprocal Rado number is 3267

Color every integer in $\{1, \ldots, N\}$ either red or blue. How large must $N$ be to guarantee a single-color solution (repetitions allowed) to the $33$-term unit-fraction equation

$$
\frac{1}{x_1} + \frac{1}{x_2} + \cdots + \frac{1}{x_{33}} = \frac{1}{y}?
$$

In Ramsey theory, this exact threshold is the two-color **reciprocal Rado number** $f_2(33)$. Here we prove in Lean 4 that $f_2(33) = 3267 = 3 \cdot 33^2$: every red-blue coloring of $\{1, \ldots, N\}$ contains a monochromatic solution if and only if $N \ge 3267$.

This settles the odd case $k = 33$ in Gaiser and Ramezanpour's Conjecture 1.3. Their Theorem 1.1 gives the general lower bound $3k^2$, and their Table 2 gives the odd cases through $k = 25$ ([Original paper](https://arxiv.org/html/2607.04373v1)).

| Field | Summary |
| --- | --- |
| Problem | Reciprocal Rado number $f_2(33) = 3267$ for $1/x_1 + \cdots + 1/x_{33} = 1/y$ (2 colors, repeated denominators allowed), Gaiser and Ramezanpour Conjecture 1.3 at $k = 33$ |
| Status | Case $k = 33$ proved in Lean 4 ($f_2(33) = 3267$). |
| Verification | `lake build && lake env leanchecker UnitFractions33` (Lean 4.36.0, stdlib only) |
| Files | [Certificate and theorem](UnitFractions33.lean) · [General lower bound](../even-unit-fractions/EvenUnitFractions/Lower.lean) |

## How the proof works

### Upper bound ($f_2(33) \le 3267$): the opposites rule and an 8-row decision list

**The big idea:** Suppose a red-blue coloring of $\{1, \ldots, 3267\}$ has no monochromatic solution. If $d$ and $33d$ ever shared a color, then $1/d = 33/(33d)$ (using $33$ copies of $1/(33d)$) would immediately be a solution. So $d$ and $33d$ must have **opposite colors** — and stepping twice by $33$ means $d$ and $33^2 d = 1089d$ must have the **same color**.

Apply this rule to the seven base values $d \in \{1, 3, 4, 9, 33, 36, 99\}$, and by symmetry call $36$ **red**. That locks in a small network of color links:

* **Fixed:** $36$ is **red**, so $1188 = 33 \cdot 36$ is **blue**.
* **Linked to $1$:** $33$ is opposite to $1$, and $1089 = 33^2 \cdot 1$ has the color of $1$.
* **Linked to $3$:** $99 = 33 \cdot 3$ is opposite to $3$, and $3267 = 33^2 \cdot 3$ has the color of $3$.
* **Linked to $4$ and $9$:** $132 = 33 \cdot 4$ is opposite to $4$, and $297 = 33 \cdot 9$ is opposite to $9$.

With these links in place, **read down the table below and stop at the first row whose condition holds.** Skipping earlier rows automatically pins down the remaining colors needed, turning that row into a monochromatic solution in the indicated color. Each $m/d$ stands for $m$ copies of $1/d$.

| First condition that holds | Color | Identity |
| --- | --- | --- |
| $3$ red and $27$ blue | Blue | $1/27 = 1/99 + 32/1188$ |
| $1$ red and $27$ red | Red | $1 = 9/27 + 24/36$ |
| $3$ red | Red | $1/3 = 2/27 + 1/33 + 8/36 + 22/3267$ |
| $1$ red | Blue | $1/3 = 6/27 + 3/33 + 24/1188$ |
| $2$ red | Red | $1/2 = 3/33 + 6/36 + 24/99$ |
| $4$ red | Blue | $1/2 = 1/3 + 21/132 + 6/1089 + 1/1188 + 4/3267$ |
| $9$ blue | Blue | $1/4 = 2/9 + 22/1089 + 9/1188$ |
| Otherwise | Blue | $1 = 2/3 + 1/4 + 23/297 + 7/1188$ |

**Worked trace:**

* Suppose the **third row** is the first match. Then $3$ is red (which also makes $3267$ red). Skipping the first row tells us $27$ cannot be blue, so $27$ is red; skipping the second row then forces $1$ to be blue, making $33$ red. Since $36$ is red, all five numbers $3, 27, 33, 36, 3267$ are red, so the third identity works.
* Suppose we fall all the way to the **last row**. Skipping rows 3, 4, 5, 6, 7 forces $3, 1, 2, 4$ to be blue and $9$ to be red. Because $9$ is red, $297 = 33 \cdot 9$ is blue, and $1188$ is always blue — making $1, 3, 4, 297, 1188$ all blue.

Every row has $33$ summands, and multiplying by $13068$ clears all denominators across the table. Together with the $7$ scaling identities $1/d = 33/(33d)$ ($d = 1, 3, 4, 9, 33, 36, 99$), these $15$ identities completely exhaust every possible red-blue coloring.

### Lower bound ($f_2(33) \ge 3267$)

The existing lower-bound coloring on $\{1, \ldots, 3266\}$ paints $\{3, \ldots, 98\}$ red and $\{1, 2\} \cup \{99, \ldots, 3266\}$ blue. The Lean theorem specializes the general lower bound to $k = 33$ and combines it with the fifteen identities above.

## Verification

[General lower bound](../even-unit-fractions/EvenUnitFractions/Lower.lean) · [Certificate and theorem](UnitFractions33.lean)

Run the following commands from this directory with Lean 4.36.0:

```sh
lake build
lake env leanchecker UnitFractions33
```
