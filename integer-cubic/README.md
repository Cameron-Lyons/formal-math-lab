# Integer cubic $z^2 + y^2 z + x^3 = 2$

Does the Diophantine equation

$$
z^2 + y^2 z + x^3 = 2
$$

have infinitely many integer solutions $(x, y, z) \in \mathbb{Z}^3$? That question remains open. The equation appears in Table 6 of Bogdan Grechuk's survey (`arXiv:2404.08518`) and in Epoch AI's FrontierMath *Small Diophantine Equations* problem, which challenges solvers to produce three integer solutions with distinct $x$ and $|x| > 10^{50}$.

Two simple algebraic rearrangements guide almost everything in this folder:

1. **Factored form:** $z(z + y^2) = 2 - x^3$. Once $x$ is chosen, finding $y$ and $z$ amounts to factoring $2 - x^3$ as $d \cdot (f/d)$ and checking whether the gap $f/d - d$ is a perfect square $y^2$.
2. **Completing the square in $z$:** multiplying by $4$ and adding $y^4$ gives

$$
(2z + y^2)^2 = y^4 - 4x^3 + 8.
$$

For each fixed $y$, this defines a smooth elliptic curve in $(x, 2z + y^2)$. To build infinitely many integer solutions systematically, one searches for **polynomial families** (polynomials $x(T), y(T), z(T) \in \mathbb{Q}[T]$ solving the equation identically) or **Pell substitutions** (rational functions of the coordinates $(u, v)$ on a Pell conic $u^2 - Dv^2 = 1$, where integer points grow exponentially via a recurrence and can amplify a single integer **seed** into infinitely many integer solutions).

The Lean 4 code and companion searches in this folder establish four partial results:

* **Ordinary polynomial degree barrier:** Any nonconstant rational polynomial family passing through an integer solution must have $\deg x \ge 6$.
* **Denominator-13 infinite family:** There is an explicit infinite family of solutions where $x$ and $z$ are integers and $y$ has reduced denominator $13$.
* **Pell amplification and obstructions:** A nonconstant **quartic Pell substitution** (where $x$ has pole order $4$ at each end of the conic) passing through an integer point would automatically generate infinitely many integer solutions, while a natural **quintic Pell substitution** is ruled out unconditionally at every coefficient height.
* **Large integer witnesses:** Three verified integer solutions have distinct $x$ and $|x| > 30{,}000{,}000$.

## At a glance

| Field | Summary |
| --- | --- |
| Problem | Diophantine equation $z^2 + y^2 z + x^3 = 2$, Grechuk (`arXiv:2404.08518`) Table 6, Epoch FrontierMath (*Small Diophantine Equations*) |
| Status | Partial results only; whether there are infinitely many integer solutions (and the $\lvert x\rvert > 10^{50}$ challenge) remains open. |
| Main theorems | `IntegerCubic.infinitely_many_with_two_integer_coordinates` ([IntegerCubic.lean](IntegerCubic.lean)); `SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart` ([pell/MixedPellAmplification.lean](pell/MixedPellAmplification.lean)); `SmallCubic.QuinticSquareObstruction.no_negative_square_lift` ([pell/QuinticSquareObstruction.lean](pell/QuinticSquareObstruction.lean)); `SmallCubic.WitnessSearch.three_large_solutions` ([pell/WitnessSearch.lean](pell/WitnessSearch.lean)) |
| Verification | `lake exe cache get && lake build && lake exe boundedSearch` (Lean 4.36.0 + mathlib v4.36.0; also `lake build SmallCubic`) |
| Prior art | Checked 24 November 2026: infinitude remains open in Grechuk Table 6, and Epoch reports polynomial families for two related cubics. Priority of the local partial obstructions and families here is unverified. |

## Polynomial family degree bound: $\deg x \ge 6$

Suppose $x, y, z \in \mathbb{Q}[T]$ form a nonconstant polynomial solution to $z^2 + y^2 z + x^3 = 2$ that takes integer values at some rational $T$. We rule out $\deg x \le 5$ in two steps: first by an exhaustive check modulo $13$, and then by showing that any rational family can be rescaled to produce a nonconstant family over $\mathbb{F}_{13}[T]$ without raising $\deg x$.

### Step 1: Exhaustion over $\mathbb{F}_{13}[T]$

Rewrite the surface in factored form:

$$
z(z + y^2) = 2 - x^3.
$$

For a fixed polynomial $x \in \mathbb{F}_{13}[T]$, set $f = 2 - x^3$ and test every polynomial divisor $d \mid f$, including nonzero scalar multiples. A divisor $d$ produces a solution if and only if $f/d - d$ is a square in $\mathbb{F}_{13}[T]$ (taking $z = d$ and $y^2 = f/d - d$).

* **Constant $x$ is impossible for a nonconstant triple:** The cubes modulo $13$ are $\{0, \pm 1, \pm 5\}$, so $2$ is not a cube modulo $13$. Hence $2 - x^3 \ne 0$ for constant $x$, which forces both $z$ and $z + y^2$ (and therefore $y$) to be constant too.
* **Nonconstant $x$ of degree $\le 5$:** Normalizing by affine changes $T \mapsto aT + b$, the Lean executable `boundedSearch` exhaustively checks all $37{,}883$ normalized nonconstant choices of $x$ with $\deg x \le 5$ and finds zero solutions.

### Step 2: Reduction from $\mathbb{Q}[T]$ to $\mathbb{F}_{13}[T]$

Why can't denominators divisible by $13$ hide a rational solution from the mod-$13$ check? We zoom in on the integer point until all denominators clear simultaneously:

1. Shift the rational point where $x, y, z$ take integer values to $T = 0$ (so all three constant terms are already integers).
2. For each nonzero positive-degree coefficient $c_i$ of $x, y, z$ in degree $i > 0$, write $c_i = 13^v u_i$ with $13 \nmid u_i$, and let $r$ be the smallest ratio $v/i$ across all such coefficients.
3. Keep $u_i \bmod 13$ whenever $v = ri$, drop all terms with $v > ri$, and reduce the constant terms modulo $13$.

Dividing the degree-$j$ coefficient identity by $13^{rj}$ (equivalently, substituting $T \mapsto 13^r T$ in a ramified extension and reducing) yields a nonconstant polynomial solution over $\mathbb{F}_{13}[T]$ without increasing $\deg x$. By Step 1, this forces $\deg x \ge 6$.

## Infinite family with integral $x, z$ and denominator-13 $y$

Although an all-integer polynomial family remains elusive, we can get remarkably close: an infinite family where $x$ and $z$ are integers and $y$ always has reduced denominator $13$.

Set

$$
y = 9k - \frac{5}{13}, \qquad z = -78k^2 + 12k - 2.
$$

These polynomials are chosen so that the right-hand side of $x^3 = 2 - z(z + y^2)$ develops a built-in cube factor $(13k - 2)^3$:

$$
2 - z(z + y^2) = \frac{18(k + 2)}{169}(13k - 2)^3.
$$

Now substitute $k = 2028n^3 - 2$ for $n = 0, 1, 2, \ldots$. Because $2028 = 12 \cdot 169$, the first factor collapses to $\frac{18 \cdot 12 \cdot 169 n^3}{169} = 216n^3 = (6n)^3$. Taking

$$
x = 6n(13k - 2)
$$

produces an infinite sequence of solutions with $x, z \in \mathbb{Z}$, strictly increasing $y$, and reduced denominator $13$ in $y$. As a quick check at $n = 0$ ($k = -2$), we get $x = 0$, $y = -\tfrac{239}{13}$, $z = -338$, and indeed $z(z + y^2) = (-338)\bigl(-338 + \tfrac{57121}{169}\bigr) = (-338)\bigl(-\tfrac{1}{169}\bigr) = 2$.

Lean proves this construction and its denominator property in `IntegerCubic.infinitely_many_with_two_integer_coordinates` and `family_y_den` inside [IntegerCubic.lean](IntegerCubic.lean).

## Pell substitutions and integer witnesses

A natural upgrade from ordinary polynomials is to parametrize curves on the surface using a **Pell conic** $u^2 - Dv^2 = 1$, whose rational parametrization in $t$ has poles only at the two points at infinity (the roots of $L = 1 - Dt^2$). A **Pell chart** expresses $(x, y, z)$ as rational functions of $t$ with powers of $L$ in the denominator.

* **Quartic Pell amplification** ([pell/MixedPellAmplification.lean](pell/MixedPellAmplification.lean)): On $u^2 - 3v^2 = 1$ with $L = 1 - 3t^2$, consider a rational polynomial identity

  $$
  A^3 + B^2 J + J^2 = 2 L^{12}, \qquad (x, y, z) = \left(\frac{A}{L^4}, \frac{B}{L^3}, \frac{J}{L^6}\right),
  $$

  with $\deg A \le 8$, $\deg B \le 6$, and $\deg J \le 12$. Lean proves (`SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart`) that if $x$ is nonconstant and $(x, y, z)$ is integral at $t = 0$, then the Pell recurrence on $u^2 - 3v^2 = 1$ clears denominators along a subsequence and generates infinitely many integer solutions.
* **Quintic Pell obstruction** ([pell/QuinticSquareObstruction.lean](pell/QuinticSquareObstruction.lean)): Lean rules out the quintic substitution $az = 2 - r^3$, $x = r - p^2 z$ for every nonzero rational $a$ on a nonsplit Pell conic whenever $r$ and $p$ have simple poles at the two conjugate ends and all coordinates are regular elsewhere, with no height bound (`SmallCubic.QuinticSquareObstruction.no_negative_square_lift`).
* **Verified integer witnesses** ([pell/WitnessSearch.lean](pell/WitnessSearch.lean)): Lean verifies three explicit integer solutions with distinct $x$ and $|x| > 30{,}000{,}000$ (`SmallCubic.WitnessSearch.three_large_solutions`). Epoch's intermediate challenge ($|x| > 10^{50}$) remains open.

## Verification

Run these commands from this directory with Lean and mathlib pinned to v4.36.0:

```sh
lake exe cache get
lake build
lake exe boundedSearch
```

* [IntegerCubic.lean](IntegerCubic.lean) contains the kernel-checked denominator-13 family, injectivity, and quadratic contact obstructions.
* [BoundedSearch.lean](BoundedSearch.lean) implements `boundedSearch` for the $\mathbb{F}_{13}[T]$ degree $\le 5$ exhaustion, which combines with the valuation reduction above.
* `lake build SmallCubic` builds the Pell library on its own.

## References

* [Bogdan Grechuk, `arXiv:2404.08518v11`, Section 5 / Table 6](https://arxiv.org/html/2404.08518v11#S5)
* [Epoch FrontierMath Open Problem: Small Diophantine Equations](https://epoch.ai/frontiermath/open-problems/small-diophantine) and [Epoch's two constructions](https://epoch.ai/files/open-problems/small-diophantine-two-families.pdf)
