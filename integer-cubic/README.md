# Integer cubic z^2 + y^2 z + x^3 = 2

Whether $z^2 + y^2 z + x^3 = 2$ has infinitely many integer solutions remains open. The equation appears in Bogdan Grechuk's Table 6 (`arXiv:2404.08518`) and Epoch AI's FrontierMath Small Diophantine Equations problem (which asks for three integer solutions with distinct $x$ and $|x| > 10^{50}$).

The Lean 4 files here prove a degree bound ($\deg x \ge 6$) for rational polynomial families passing through an integer solution, give an infinite family with integral $x, z$ and $y$ of reduced denominator 13, prove a Pell-curve amplification theorem along with a height-free quintic obstruction, and verify three integer solutions with distinct $x$ and $|x| > 30{,}000{,}000$.

| Field | Summary |
| --- | --- |
| Problem | Diophantine equation $z^2 + y^2 z + x^3 = 2$, Grechuk (`arXiv:2404.08518`) Table 6, Epoch FrontierMath (*Small Diophantine Equations*) |
| Status | Partial results only; infinitude of integer solutions (and the $|x| > 10^{50}$ challenge) remains open. |
| Main theorems | `IntegerCubic.infinitely_many_with_two_integer_coordinates` ([IntegerCubic.lean](IntegerCubic.lean)); `SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart` ([pell/MixedPellAmplification.lean](pell/MixedPellAmplification.lean)); `SmallCubic.QuinticSquareObstruction.no_negative_square_lift` ([pell/QuinticSquareObstruction.lean](pell/QuinticSquareObstruction.lean)); `SmallCubic.WitnessSearch.three_large_solutions` ([pell/WitnessSearch.lean](pell/WitnessSearch.lean)) |
| Verification | `lake exe cache get && lake build && lake exe boundedSearch` (Lean 4.36.0 + mathlib v4.36.0; also `lake build SmallCubic`) |
| Prior art | Checked 24 November 2026: infinitude remains open in Grechuk Table 6; Epoch reports polynomial families for two related cubics. Priority of the local partial obstructions and families is unverified. See [PRIOR_ART.md](../PRIOR_ART.md). |

## Polynomial family degree bound: deg(x) >= 6

Suppose $x, y, z \in \mathbb{Q}[T]$ form a nonconstant polynomial solution to $z^2 + y^2 z + x^3 = 2$ taking integer values simultaneously at some rational $T$.

Step 1: reduce modulo 13. Rewrite the equation as

$$
z(z + y^2) = 2 - x^3.
$$

For a fixed polynomial $x \in \mathbb{F}_{13}[T]$, set $f = 2 - x^3$ and test each polynomial divisor $d \mid f$ (including scalar multiples); $d$ gives a solution iff $f / d - d$ is a square in $\mathbb{F}_{13}[T]$ (taking $z = d$ and $y^2 = f/d - d$). The Lean executable `boundedSearch` checks all 37,883 normalized choices of nonconstant $x$ with $\deg x \le 5$ (after affine reparametrization $T \mapsto aT + b$) and finds no solutions. If $x$ is constant, then $2 - x^3 \ne 0$ (since 2 is not a cube mod 13), forcing $y, z$ constant too.

Step 2: pass from $\mathbb{Q}[T]$ to $\mathbb{F}_{13}[T]$. Translate the integral specialization to $T = 0$. For every nonzero positive-degree coefficient $c_i$ of $x, y, z$ in degree $i$, write $c_i = 13^v u_i$ with $13 \nmid u_i$, and let $r$ be the minimum ratio $v / i$. Retain $u_i \bmod 13$ whenever $v = ri$, discard terms with $v > ri$, and reduce constant terms mod 13. Dividing the degree-$j$ coefficient identity by $13^{rj}$ yields a nonconstant solution over $\mathbb{F}_{13}[T]$ without increasing $\deg x$. Hence $\deg x \ge 6$.

## Infinite family with integral x, z and denominator-13 y

Put $y = 9k - \tfrac{5}{13}$ and $z = -78k^2 + 12k - 2$. Expanding gives

$$
2 - z(z + y^2) = \frac{18(k + 2)}{169}(13k - 2)^3.
$$

Setting $k = 2028n^3 - 2$ for $n = 0, 1, 2, \ldots$ makes the first factor $(6n)^3$, so $x = 6n(13k - 2)$ yields an infinite family of solutions with $x, z \in \mathbb{Z}$, strictly increasing $y$, and reduced denominator 13 in $y$ (`IntegerCubic.infinitely_many_with_two_integer_coordinates`, `family_y_den` in [IntegerCubic.lean](IntegerCubic.lean)).

## Pell substitutions and integer witnesses

* Quartic Pell amplification ([pell/MixedPellAmplification.lean](pell/MixedPellAmplification.lean)): on $u^2 - 3v^2 = 1$ with $L = 1 - 3t^2$, consider a rational polynomial identity

  $$
  A^3 + B^2 J + J^2 = 2 L^{12}, \qquad (x, y, z) = \left(\frac{A}{L^4}, \frac{B}{L^3}, \frac{J}{L^6}\right),
  $$

  with $\deg A \le 8$, $\deg B \le 6$, $\deg J \le 12$. Lean proves (`SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart`) that if $x$ is nonconstant and the triple at $t = 0$ is integral, then the Pell recurrence generates infinitely many integer solutions. At the seed $(0, 1, 1)$, exact modular searches ruled out over 21 million candidate first coordinates in each of two bases within height bound 171 ([pell/QuarticFreeMark.md](pell/QuarticFreeMark.md)).
* Quintic Pell obstruction ([pell/QuinticSquareObstruction.lean](pell/QuinticSquareObstruction.lean)): Lean rules out the quintic substitution $az = 2 - r^3$, $x = r - p^2 z$ for every nonzero rational $a$ on a nonsplit Pell conic when $r, p$ have simple poles at the two conjugate ends and all coordinates are regular elsewhere, at every coefficient height (`SmallCubic.QuinticSquareObstruction.no_negative_square_lift`; see [pell/QuinticFactorSearch.md](pell/QuinticFactorSearch.md)).
* Verified integer witnesses ([pell/WitnessSearch.lean](pell/WitnessSearch.lean)): Lean verifies three explicit integer solutions with distinct $x$ and $|x| > 30{,}000{,}000$ (`SmallCubic.WitnessSearch.three_large_solutions`; see [pell/WitnessSearch.md](pell/WitnessSearch.md)). Epoch's intermediate challenge ($|x| > 10^{50}$) remains open.

## Verification

From this directory with Lean and mathlib pinned to v4.36.0:

```sh
lake exe cache get
lake build
lake exe boundedSearch
```

* [IntegerCubic.lean](IntegerCubic.lean) contains the kernel-checked denominator-13 family, injectivity, and quadratic contact obstructions.
* [BoundedSearch.lean](BoundedSearch.lean) implements `boundedSearch` for the $\mathbb{F}_{13}[T]$ degree $\le 5$ exhaustion (combined with the valuation reduction above).
* `lake build SmallCubic` builds the Pell library standalone.
* Additional search scripts under [pell/](pell/) document their own commands (mostly Python with `python-flint==0.9.0` via `uv`, and where noted C++17, PARI/GP, or Z3).

## References

* [Bogdan Grechuk, `arXiv:2404.08518v11`, §5 / Table 6](https://arxiv.org/html/2404.08518v11#S5)
* [Epoch FrontierMath Open Problem: Small Diophantine Equations](https://epoch.ai/frontiermath/open-problems/small-diophantine) and [Epoch's two constructions](https://epoch.ai/files/open-problems/small-diophantine-two-families.pdf)
* [Prior-art audit](../PRIOR_ART.md)
