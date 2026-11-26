# Two prescribed values on the Pell conic

Let $x, y, z$ be rational polynomials on $u^2 - 3v^2 = 1$ of total degrees at most $4, 3, 6$, respectively, satisfying $z^2 + y^2 z + x^3 = 2$ identically and taking $(0, 1, 1)$ at $(1, 0)$. **Neither $(1, 0, -1)$ nor $(-2, 3, 1)$ can occur at $(2, 1)$.** Both obstructions already hold over $\mathbb{Q}_2$.

## Why the finite tests cover arbitrary denominators

Set $w = u - 1 - v$, which vanishes at both marked points ($v = 0$ at the first and $v = 1$ at the second). Because

$$
v^2 = (1 + w)v + w + \frac{w^2}{2},
$$

each coordinate of degree bound $d$ writes uniquely as $P(w) + vQ(w)$ with $\deg P \le d$ and $\deg Q < d$. The two marks fix the integer constants $P(0)$ and $Q(0)$.

Let $h$ be the maximum of $-v_2(a_i)/i$ over all nonzero positive-degree coefficients $a_i$ in the six polynomials. (If all six polynomials are constant, the integral case below applies directly.)

* When $h \le 1/2$, every coefficient satisfies $2^{\lfloor i/2 \rfloor} a_i \in \mathbb{Z}_2$. Since $w^2/2 = v^2 - v - (1 + v)w$, every term $a_i w^i$ lands in the original 2-integral Pell-coordinate ring without raising the degree bound. Writing each coordinate as $f(v) + wq(v)$ with marked values $a, b$ gives $f(v) = a + (b - a)v + v(v - 1)r(v)$. Comparing coefficients yields a contradiction modulo 4 for $(1, 0, -1)$ and modulo 4096 for $(-2, 3, 1)$ (while the latter does admit an explicit model modulo 2048). See [TwoPointMarkedPolynomial.lean](TwoPointMarkedPolynomial.lean) for the normal form and [two_point_alternate_two.lean](two_point_alternate_two.lean) for the mod-4096 proof and mod-2048 witness.
* When $h > 1/2$, write $h = k + j/e$ in reduced form (allowing $j = 0, e = 1$). An index $i$ achieving the maximum satisfies $e \mid i$, so $e \le 6$. Switch to the normalized basis $E_i = w^i / 2^{\lfloor hi \rfloor}$. Every coefficient becomes 2-integral, at least one positive-index coefficient with $e \mid i$ is odd, and the basis multiplies by

  $$
  E_a E_b = 2^{\lfloor h(a + b) \rfloor - \lfloor ha \rfloor - \lfloor hb \rfloor} E_{a + b},
  $$

  whose exponent depends only on the fractional part $j/e$. In the rule for $v^2$, multiplying by $w$ and $w^2/2$ brings in extra factors of 2. When $k \ge 1$, writing $2^k = 2H$ and $2^{2k - 1} = 2H^2$ with an arbitrary residue $H$ covers all $k \ge 1$ in a single test for each fraction $j/e$. The remaining cases have $k = 0$ and $j/e > 1/2$, where all products stay integral in this basis.

There are 12 reduced fractions in $[0, 1)$ with denominator at most 6: all 12 need the $k \ge 1$ check, and 5 also need the $k = 0$ check. For each target, [TwoPointBalanced.lean](TwoPointBalanced.lean) proves that all 17 systems are inconsistent modulo 8 and that the list exhausts every admissible fraction. The theorem takes all 23 unknown coefficients and $H$ as inputs, assuming the cubic identity and an odd coefficient at an active index. An independent Z3 script in [two_point_two_adic.py](two_point_two_adic.py) reproduces all 17 checks. Passing from rational 2-adic valuations to these 17 normalized systems is the written step above.

For the first target, a stronger statement holds: if all three values at $(2, 1)$ are integral at 2, then $x(2, 1)$ must be even. Modulo 4, the equation permits only four odd-$x$ triples, and an exhaustive Python check matches every resulting correction matrix to one of 26 Lean-certified inconsistent subsystems; see [TwoPointPrimaryTwo.md](TwoPointPrimaryTwo.md). For the alternate target, the same proof rules out every integral triple congruent to $(-2, 3, 1) \pmod{4096}$, since the tests only read the marked values modulo a divisor of 4096; see [TwoPointAlternateTwo.md](TwoPointAlternateTwo.md).

## Exact equations and the recurrence

In the rational chart $t = v/(u + 1)$ with $L = 1 - 3t^2$, write $x = X/L^4$, $y = Y/L^3$, $z = Z/L^6$, with numerator degrees at most $8, 6, 12$. Mapping the two marks $t = 0, 1/3$ to $0, \infty$ via $t = s/(1 + 3s)$ changes the denominator to $D = 1 + 6s + 6s^2$. Setting $W = 2Z + Y^2$ turns the identity into

$$
W^2 = Y^4 + 8 D^{12} - 4 X^3.
$$

The two marks fix the constant and leading coefficients of $X, Y, W$; in particular $W_0 = 3$ and $W_{12} = 6^6 (2z_1 + y_1^2)$, both nonzero for both targets. Matching coefficients $1, \ldots, 6$ solves sequentially for $W_1, \ldots, W_6$ by dividing by $2W_0$, and matching coefficients $23, \ldots, 19$ solves for $W_{11}, \ldots, W_7$ by dividing by $2W_{12}$. The 12 middle coefficients yield 12 exact equations over $\mathbb{Q}$ in the 7 free coefficients of $X$ and 5 of $Y$, with $Z = (W - Y^2)/2$; see [two_point_elimination.py](two_point_elimination.py).

For any future chart through an integral seed whose $x$-value changes at $t = 1/3$, Lean proves in [MixedPellAmplification.lean](MixedPellAmplification.lean) that a rational polynomial identity of these degrees generates infinitely many distinct integer solutions: the recurrence $(u, v) \mapsto (2u + 3v, u + 2v)$ returns to the seed modulo any common denominator along an infinite subsequence.

## Residue calculations at 7 and 13

Having two marked points also controls denominators at 13. In the $t$-chart, $c = 0$ and $c = 1/3$ reduce to distinct points of $\mathbb{F}_{13}$, and $L(c)$ is a unit at both. Suppose some coefficient of $X, Y, Z$ has negative 13-adic valuation. Integral shifts preserve that property, so at either center $c$ the positive-index Taylor coefficients have a positive maximum slope $h = \max(-v_{13}(a_i)/i)$. Rescaling $t = c + \lambda T$ with $v_{13}(\lambda) = h$ in a totally ramified extension makes $L$ reduce to the nonzero constant $L(c)$ and yields a nonconstant ordinary polynomial solution over $\mathbb{F}_{13}$. By [OrdinaryPolynomial.md](OrdinaryPolynomial.md), the reduced $x$-coordinate must have degree at least 6.

Therefore, at each center $c$, some Taylor coefficient $a_k$ of $X$ with $k \ge 6$ satisfies $v_{13}(a_k) = -kh$, while every nonzero coefficient at $i < k$ satisfies $v_{13}(a_i) \ge -ih > -kh$. Scale $X$ by a power of 13 so its minimum coefficient valuation is 0 (integral shifts preserve that minimum). Its nonzero reduction modulo 13 would then vanish to order at least 6 at two distinct points despite having degree at most 8, which is impossible. Thus every rational solution of arbitrary height is 13-integral and appears in the mod-13 census. Lean proves the multiplicity and slope lemmas in [TwoPointDegree.lean](TwoPointDegree.lean).

Fixing both $x$-values leaves 7 free coefficients in $X$. For each of the $p^7$ candidates, [two_point_census.py](two_point_census.py) factors $2L^{12} - X^3$, checks every degree-12 divisor $Z$ with $Z(0) = 1$, and tests whether the complementary divisor minus $Z$ is a square matching both $y$-values. At $p = 7$ and $p = 13$, $2L^{12} - X^3$ keeps full leading degree (2 is not a cube) and nonzero constant and marked values; candidates that lose poles modulo $p$ are included. The census finds 2 and 1 residue triples modulo 7, and 4 and 4 modulo 13, for the first and second targets respectively. [two_point_lifts.py](two_point_lifts.py) lifts every residue in [two_point_residues.jsonl](two_point_residues.jsonl) to $p^{50}$. The mod-2 obstruction shows that none of these local lifts can come from a rational substitution.

As an extra check, $(8, 7, -15)$ lies on the cubic surface and its quartic system has a solution modulo 4096 (verified in [two_point_alternate_two.lean](two_point_alternate_two.lean)). However, testing all $5^7 = 78{,}125$ numerators $X$ over $\mathbb{F}_5$ in [two_point_census.py](two_point_census.py) finds zero models, so any rational chart through $(8, 7, -15)$ would need a denominator divisible by 5 in the $t$-chart.

To reproduce all checks, run:

```sh
lake -d .. build
uv run --with z3-solver==4.15.4.0 python two_point_two_adic.py
uv run --with python-flint==0.9.0 python two_point_primary_two.py
uv run --with python-flint==0.9.0 python two_point_alternate_balanced_two.py
uv run --with python-flint==0.9.0 python two_point_elimination.py --target 1
uv run --with python-flint==0.9.0 python two_point_census.py --prime 5 --endpoint 8 7 -15
uv run --with python-flint==0.9.0 python two_point_lifts.py two_point_residues.jsonl --precision 50
```
