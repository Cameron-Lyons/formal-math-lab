# Integer cubic z^2 + y^2 z + x^3 = 2

It is still an open question whether $z^2 + y^2 z + x^3 = 2$ has infinitely many integer solutions. The equation appears in Table 6 of Bogdan Grechuk's survey (`arXiv:2404.08518`) and in Epoch AI's FrontierMath *Small Diophantine Equations* problem, which asks for three integer solutions with distinct $x$ and $|x| > 10^{50}$.

The Lean 4 code in this folder establishes four partial results:

* Any nonconstant rational polynomial family passing through an integer solution must have $\deg x \ge 6$.
* There is an infinite family of solutions where $x$ and $z$ are integers and $y$ has reduced denominator 13.
* A nonconstant quartic Pell substitution through an integer point would generate infinitely many integer solutions, while a natural quintic Pell substitution is ruled out at every coefficient height.
* Three verified integer solutions have distinct $x$ and $|x| > 30{,}000{,}000$.

| Field | Summary |
| --- | --- |
| Problem | Diophantine equation $z^2 + y^2 z + x^3 = 2$, Grechuk (`arXiv:2404.08518`) Table 6, Epoch FrontierMath (*Small Diophantine Equations*) |
| Status | Partial results only; whether there are infinitely many integer solutions (and the $\lvert x\rvert > 10^{50}$ challenge) remains open. |
| Main theorems | `IntegerCubic.infinitely_many_with_two_integer_coordinates` ([IntegerCubic.lean](IntegerCubic.lean)); `SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart` ([pell/MixedPellAmplification.lean](pell/MixedPellAmplification.lean)); `SmallCubic.QuinticSquareObstruction.no_negative_square_lift` ([pell/QuinticSquareObstruction.lean](pell/QuinticSquareObstruction.lean)); `SmallCubic.WitnessSearch.three_large_solutions` ([pell/WitnessSearch.lean](pell/WitnessSearch.lean)) |
| Verification | `lake exe cache get && lake build && lake exe boundedSearch` (Lean 4.36.0 + mathlib v4.36.0; also `lake build SmallCubic`) |
| Prior art | Checked 24 November 2026: infinitude remains open in Grechuk Table 6, and Epoch reports polynomial families for two related cubics. Priority of the local partial obstructions and families here is unverified. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Polynomial family degree bound: deg(x) >= 6

Suppose $x, y, z \in \mathbb{Q}[T]$ form a nonconstant polynomial solution to $z^2 + y^2 z + x^3 = 2$ that takes integer values at some rational $T$.

Step 1: check modulo 13. Rewrite the equation as

$$
z(z + y^2) = 2 - x^3.
$$

For a fixed polynomial $x \in \mathbb{F}_{13}[T]$, let $f = 2 - x^3$ and test every polynomial divisor $d \mid f$, including scalar multiples. A divisor $d$ gives a solution if and only if $f/d - d$ is a square in $\mathbb{F}_{13}[T]$ (setting $z = d$ and $y^2 = f/d - d$). After normalizing by affine changes $T \mapsto aT + b$, the Lean executable `boundedSearch` checks all 37,883 normalized nonconstant choices of $x$ with $\deg x \le 5$ and finds no solutions. If $x$ is constant, then $2 - x^3 \ne 0$ because 2 is not a cube modulo 13, which forces $y$ and $z$ to be constant too.

Step 2: reduce from $\mathbb{Q}[T]$ to $\mathbb{F}_{13}[T]$. Shift the rational point with integer values to $T = 0$. For each nonzero positive-degree coefficient $c_i$ of $x, y, z$ in degree $i$, write $c_i = 13^v u_i$ with $13 \nmid u_i$, and let $r$ be the smallest ratio $v/i$. Keep $u_i \bmod 13$ whenever $v = ri$, drop terms with $v > ri$, and reduce the constant terms modulo 13. Dividing the degree-$j$ coefficient identity by $13^{rj}$ produces a nonconstant solution over $\mathbb{F}_{13}[T]$ without raising $\deg x$. By Step 1, this forces $\deg x \ge 6$.

## Infinite family with integral x, z and denominator-13 y

Set $y = 9k - \tfrac{5}{13}$ and $z = -78k^2 + 12k - 2$. Expanding gives

$$
2 - z(z + y^2) = \frac{18(k + 2)}{169}(13k - 2)^3.
$$

Choosing $k = 2028n^3 - 2$ for $n = 0, 1, 2, \ldots$ turns the first factor into $(6n)^3$. Then $x = 6n(13k - 2)$ gives an infinite family of solutions with $x, z \in \mathbb{Z}$, strictly increasing $y$, and reduced denominator 13 in $y$. Lean proves this in `IntegerCubic.infinitely_many_with_two_integer_coordinates` and `family_y_den` inside [IntegerCubic.lean](IntegerCubic.lean).

## Pell substitutions and integer witnesses

* Quartic Pell amplification ([pell/MixedPellAmplification.lean](pell/MixedPellAmplification.lean)): on $u^2 - 3v^2 = 1$ with $L = 1 - 3t^2$, consider a rational polynomial identity

  $$
  A^3 + B^2 J + J^2 = 2 L^{12}, \qquad (x, y, z) = \left(\frac{A}{L^4}, \frac{B}{L^3}, \frac{J}{L^6}\right),
  $$

  with $\deg A \le 8$, $\deg B \le 6$, and $\deg J \le 12$. Lean proves (`SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart`) that if $x$ is nonconstant and the triple at $t = 0$ is integral, the Pell recurrence generates infinitely many integer solutions. Through the seed $(0, 1, 1)$, exact modular searches ruled out over 21 million candidate first coordinates in each of two bases up to height 171; see [pell/QuarticFreeMark.md](pell/QuarticFreeMark.md).
* Quintic Pell obstruction ([pell/QuinticSquareObstruction.lean](pell/QuinticSquareObstruction.lean)): Lean rules out the quintic substitution $az = 2 - r^3$, $x = r - p^2 z$ for every nonzero rational $a$ on a nonsplit Pell conic when $r$ and $p$ have simple poles at the two conjugate ends and all coordinates are regular elsewhere, with no height bound (`SmallCubic.QuinticSquareObstruction.no_negative_square_lift`; see [pell/QuinticFactorSearch.md](pell/QuinticFactorSearch.md)).
* Verified integer witnesses ([pell/WitnessSearch.lean](pell/WitnessSearch.lean)): Lean verifies three explicit integer solutions with distinct $x$ and $|x| > 30{,}000{,}000$ (`SmallCubic.WitnessSearch.three_large_solutions`; see [pell/WitnessSearch.md](pell/WitnessSearch.md)). Epoch's intermediate challenge ($|x| > 10^{50}$) remains open.

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
* Additional search scripts under [pell/](pell/) document their own commands (mostly Python with `python-flint==0.9.0` via `uv`, and where noted C++23, PARI/GP, or Z3).

## References

* [Bogdan Grechuk, `arXiv:2404.08518v11`, Section 5 / Table 6](https://arxiv.org/html/2404.08518v11#S5)
* [Epoch FrontierMath Open Problem: Small Diophantine Equations](https://epoch.ai/frontiermath/open-problems/small-diophantine) and [Epoch's two constructions](https://epoch.ai/files/open-problems/small-diophantine-two-families.pdf)
* [Prior-art audit](../PRIOR_ART.md)
