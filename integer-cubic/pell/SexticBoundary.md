# Ordinary sextic substitutions through an integer point

One of the simplest ways to construct infinitely many integer solutions to $z^2 + y^2 z + x^3 = 2$ would be an *ordinary* one-variable rational polynomial family $x(t), y(t), z(t) \in \mathbb{Q}[t]$ that takes integer values together at some rational point $t_0$. Earlier work ([OrdinaryPolynomial.md](OrdinaryPolynomial.md)) proved that any nonconstant family must have $\deg x \ge 6$.

Here we push that degree barrier past $6$ for almost every seed: **if $\deg x \le 6$ and $x(t_0) \not\equiv 3 \pmod 5$, then the polynomial family must be constant.** In particular, any ordinary polynomial family through $(0, 1, 1)$ must have $\deg x \ge 7$. The proof combines exact finite-field checks in [SexticSearch.py](SexticSearch.py), a two-stage $5$-adic valuation argument, and a Lean proof of the boundary obstruction in [SexticBoundary.lean](SexticBoundary.lean).

For the remaining congruence class $x(t_0) \equiv 3 \pmod 5$, an independent $13$-adic census eliminates $(1, 0, 1)$ and narrows the allowed seeds to $116$ of the $130$ points over $\mathbb{F}_{13}$. At the surviving small seed $(-2, 3, 1)$, lifting uniquely modulo $13^{700}$ proves that every one of the $18$ free coefficients (in the chart normalized by $x'(0) = 1$) must have rational height strictly greater than $10^{388}$.

## Forced degree patterns at $\deg x = 6$

Degrees up to $5$ are ruled out for every integer seed in [OrdinaryPolynomial.md](OrdinaryPolynomial.md). Now suppose $\deg x = 6$.

In the factored equation $z(z + y^2) = 2 - x^3$, every irreducible factor over $\mathbb{Q}[t]$ has degree divisible by $3$ (because its residue field contains $\sqrt[3]{2}$), and neither $z$ nor $z + y^2$ can be constant (by the genus-$1$ argument). Consequently, their degrees are positive multiples of $3$ summing to $18$, and if they differ, the larger degree equals $2\deg y$ and must be even.

Up to the involution $z \mapsto -z - y^2$, only **two** degree pairs survive:

* **Degree pair $(6, 12)$:** Here $\deg y = 6$ and the smaller choice of $z$ has degree $6$. Balancing denominators at $13$ produces a nonconstant solution over $\mathbb{F}_{13}$ with all three degrees at most $6$, which is already ruled out in [CubicPellAt13.md](CubicPellAt13.md#ordinary-polynomial-solutions-modulo-13).
* **Degree pair $(9, 9)$:** Here $\deg y \le 4$. Completing the square via $W = 2z + y^2$ turns the surface equation into
  $$
  W^2 + 4x^3 = y^4 + 8.
  $$

## Stage 1: First rescaling at 5 (forced degree drop)

Shift the integer point $t_0$ to $0$, and let $h = \max(-v_5(c_i)/i)$ over all nonzero positive-degree coefficients of $x, y, z$. Pick $\lambda$ with $v(\lambda) = h$ in a totally ramified extension and substitute $t = \lambda T$. Then all coefficients become $5$-integral, at least one nonconstant coefficient becomes a $5$-adic unit, and the residue field remains $\mathbb{F}_5$.

Why must the reduced polynomial $\bar x$ be nonconstant? Because $x^3 \equiv 2 \pmod 5$ holds if and only if $x \equiv 3 \pmod 5$, our hypothesis $x(0) \not\equiv 3 \pmod 5$ guarantees $2 - \bar x(0)^3 \ne 0$. If $\bar x$ were constant, $2 - \bar x^3$ would be a nonzero constant, forcing both factors $\bar z, \bar z + \bar y^2$ and hence $\bar y$ to be constant too—contradicting the surviving unit nonconstant coefficient.

Modulo affine transformations $T \mapsto cT + d$ ($c \ne 0$), there are **4,075** orbits of nonconstant polynomials $\bar x \in \mathbb{F}_5[T]$ with $\deg \bar x \le 6$. For each representative, [SexticSearch.py](SexticSearch.py) factors $2 - \bar x^3$, tests every divisor $\bar z$ of degree at most $9$ (including all scalar multiples), and checks whether $(2 - \bar x^3)/\bar z - \bar z$ is a square of degree at most $8$.

The census finds exactly **12** pairs, and **every single one** has:
* degree profile $(\deg \bar x, \deg \bar y, \deg \bar z) = (4, 3, 6)$ (so $x$ loses two degrees modulo $5$), and
* leading coefficient of $\bar x$ in $\{2, 4\}$ (which is invariant under $T \mapsto cT + d$ because $c^4 = 1$ in $\mathbb{F}_5^\times$).

## Stage 2: Second rescaling at infinity (boundary obstruction)

Because $\deg x = 6$ in characteristic zero yet $\deg \bar x = 4$ modulo $5$, the top two coefficients of $x$ vanish modulo the maximal ideal. Reversing the balanced polynomials moves those hidden top coefficients to $s = 0$, where a second valuation rescaling creates a degree-$6$ boundary identity over $\mathbb{F}_5$ that has no nontrivial solution.

1. **Reversal.** Set $A(s) = s^6 x(1/s)$, $B(s) = s^4 y(1/s)$, and $E(s) = s^9 W(1/s)$. They satisfy
   $$
   E^2 + 4 A^3 = s^2 B^4 + 8 s^{18}.
   $$
   Modulo the maximal ideal, $A$ starts with $a s^2$ ($a \in \{2, 4\}$), $B$ starts with $b s$ ($b \ne 0$), and $E$ is divisible by $s^3$. Since $\deg x = 6$ in characteristic zero, $A_0 \ne 0$.
2. **Second slope.** Taking $v(0) = +\infty$, set
   $$
   r = \min\left\{\frac{v(A_0)}{2},\, v(A_1),\, v(B_0),\, \frac{v(E_0)}{3},\, \frac{v(E_1)}{2},\, v(E_2)\right\} > 0.
   $$
   Pick $\mu$ of valuation $r$ in a further totally ramified extension, substitute $s = \mu T$, and divide $A, B, E$ by $\mu^2, \mu, \mu^3$, respectively. Every coefficient remains integral, at least one lower coefficient survives by the minimality of $r$, and $8 s^{18}/\mu^6$ drops out modulo $\mu$, leaving the reduced identity over $\mathbb{F}_5[T]$:
   $$
   e(T)^2 = T^2 (bT + w)^4 - 4(aT^2 + vT + u)^3.
   $$
3. **Lean proof of the boundary contradiction.** In [SexticBoundary.lean](SexticBoundary.lean), Lean proves $u = v = w = 0$ for all $a \in \{2, 4\}$ and $b \ne 0$ by evaluating the right-hand side at all five elements of $\mathbb{F}_5$ and at $\sqrt{2}, 2\sqrt{2} \in \mathbb{F}_{25}$ (where the norm of a square must be a square in $\mathbb{F}_5$). Independently, direct polynomial square-root tests rule out all $2 \cdot 4 \cdot (5^3 - 1) = 992$ cases with a surviving lower coefficient in $A$ or $B$.
4. **Closing the contradiction.** Once $u = v = w = 0$, $e(T)^2$ is a constant multiple of $T^6$, so $e$ is either $0$ or a multiple of $T^3$. That forces all lower coefficients of $E$ to vanish as well, contradicting the choice of $r$.

## Remaining seeds and the mod-13 sieve

When $x(t_0) \equiv 3 \pmod 5$, the first reduction can have constant $\bar x = 3$ with $\bar z = 0$ or $\bar z = -\bar y^2$. Every reduction with nonconstant $\bar x$ is still ruled out by the two-stage proof above, leaving only those two lines.

Independently, balancing at $p = 13$ restricts the marked triple to **116** of the **130** points on the surface over $\mathbb{F}_{13}$:

1. Because $2$ is not a cube modulo $13$ and degrees below $6$ are ruled out, any balanced reduction over $\mathbb{F}_{13}$ must have $\deg \bar x = 6$.
2. Shift $T$ to kill the $T^5$ coefficient, and scale $T$ and $\bar x$ (by a cube root of unity) so the leading coefficient $\bar x_6$ lies in $\{1, 2\}$.
3. Both factors of $2 - \bar x^3$ have degree $9$ and share the same leading coefficient (since $\deg \bar y \le 4$), whose square equals $-\bar x_6^3$; this forces $\bar x_6 = 1$.
4. Factoring across all $13^5$ remaining choices of $\bar x$ yields **24** solutions (counted by divisor and leading scalar). Evaluating at every element of $\mathbb{F}_{13}$, both signs of $\bar y$, and all cube-root twists produces the **116** allowed seeds.

This excludes $(1, 0, 1)$ at $13$, while still allowing $(-2, 3, 1)$. Reproduce both finite checks with:

```sh
uv run --with python-flint==0.9.0 SexticSearch.py --seeds-at-13
```

## The exceptional seed $(-2, 3, 1)$

At $(-2, 3, 1)$, shifting each degree-$6$ mod-$13$ solution to every parameter value hitting the mark (and restoring all cube-root twists and signs) always leaves $x'(0) \ne 0 \pmod{13}$.

1. **Canonical normalization.** In any rational sextic map through $(-2, 3, 1)$, the balancing radius at $13$ must therefore be an integer (because the linear coefficient of $x$ becomes a $13$-adic unit). A unique rational rescaling sets $x'(0) = 1$ while keeping all coefficients $13$-integral, collapsing all mod-$13$ candidates to a **single** triple.
2. **Unique lift modulo $13^{700}$.** Fixing the constant terms at $(-2, 3, 1)$ and $x_1 = 1$ leaves $18$ unknowns ($x_2, \ldots, x_6$, $y_1, \ldots, y_4$, $z_1, \ldots, z_9$) and $18$ equations from the nonconstant coefficients of $x^3 + zy^2 + z^2 - 2$. The Jacobian is invertible modulo $13$, so the $13$-adic lift is unique. [SexticSearch.py](SexticSearch.py) lifts $699$ times and verifies the residual modulo $M = 13^{700}$.
3. **Height lower bound $> 10^{388}$ for every coefficient.** For **each of the 18 coefficients**, if it is rational in lowest terms, the larger of its absolute numerator and positive denominator must exceed $10^{388}$. To prove this for a computed residue $r \bmod M$, the script finds two linearly independent integer pairs $(a_i, b_i)$ satisfying
   $$
   a_i \equiv r b_i \pmod M \qquad \text{and} \qquad (|a_i| + |b_i|) \cdot 10^{388} < M.
   $$
   Any rational $A/B$ of height at most $10^{388}$ matching $r \bmod M$ makes $a_i B - b_i A$ divisible by $M$ yet strictly smaller than $M$ in absolute value, forcing $a_i B - b_i A = 0$ for both independent pairs and hence $(A, B) = (0, 0)$—a contradiction. The script checks all congruences, bounds, and linear independence exactly (in the coordinate normalized by $x'(0) = 1$).

Reproduce the marked lifts and height certificates with:

```sh
uv run --with python-flint==0.9.0 SexticSearch.py --exceptional-seed
```
