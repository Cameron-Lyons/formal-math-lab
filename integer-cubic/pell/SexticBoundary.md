# Ordinary sextic substitutions through an integer point

Suppose $x, y, z \in \mathbb{Q}[t]$ satisfy $z^2 + y^2 z + x^3 = 2$ identically and take integer values together at some rational $t_0$. **If $\deg x \le 6$ and $x(t_0) \not\equiv 3 \pmod 5$, then the family is constant.** In particular, any ordinary polynomial family through $(0, 1, 1)$ must have $\deg x \ge 7$. The proof combines exact finite-field checks in [SexticSearch.py](SexticSearch.py), a written valuation argument, and a Lean proof of the boundary obstruction in [SexticBoundary.lean](SexticBoundary.lean).

## Degree patterns

Degrees up to 5 are ruled out for every integer seed in [OrdinaryPolynomial.md](OrdinaryPolynomial.md). Now suppose $\deg x = 6$. Every irreducible factor of $z(z + y^2) = 2 - x^3$ has degree divisible by 3 because its residue field contains $\sqrt[3]{2}$, and neither $z$ nor $z + y^2$ can be constant (by the genus-1 argument). Thus their degrees are positive multiples of 3 summing to 18, and if they differ, the larger degree equals $2\deg y$ and must be even.

Up to the involution $z \mapsto -z - y^2$, only two degree pairs remain: $(6, 12)$ and $(9, 9)$.

* For $(6, 12)$, $\deg y = 6$ and the smaller choice of $z$ has degree 6. Balancing at 13 gives a nonconstant solution over $\mathbb{F}_{13}$ with all three degrees at most 6, already ruled out in [CubicPellAt13.md](CubicPellAt13.md#ordinary-polynomial-solutions-modulo-13).
* For $(9, 9)$, $\deg y \le 4$. Setting $W = 2z + y^2$ gives $W^2 + 4x^3 = y^4 + 8$.

## First scale at 5

Shift $t_0$ to 0, and let $h$ be the largest value of $-v_5(c_i)/i$ over all nonzero positive-degree coefficients of $x, y, z$. Pick $\lambda$ with $v(\lambda) = h$ in a totally ramified extension and substitute $t = \lambda T$. All coefficients become 5-integral, at least one nonconstant coefficient is a unit, and the residue field remains $\mathbb{F}_5$. If $\bar x$ were constant, $x(0) \not\equiv 3 \pmod 5$ would make $2 - \bar x^3 \ne 0$, forcing both factors and $\bar y$ to be constant too. So $\bar x$ is nonconstant.

Under $T \mapsto cT + d$ ($c \ne 0$), there are 4,075 orbits of nonconstant polynomials $\bar x \in \mathbb{F}_5[T]$ of degree at most 6. For each representative, [SexticSearch.py](SexticSearch.py) factors $2 - \bar x^3$, tries every divisor $\bar z$ of degree at most 9 (including all scalar multiples), and checks whether $(2 - \bar x^3)/\bar z - \bar z$ is a square of degree at most 8. It finds 12 pairs, every one with degree profile $(\deg \bar x, \deg \bar y, \deg \bar z) = (4, 3, 6)$. Their leading coefficients in $\bar x$ always lie in $\{2, 4\}$ (invariant under $T \mapsto cT + d$ since $c^4 = 1$ in $\mathbb{F}_5^\times$).

## Second scale at infinity

Reverse the balanced polynomials by setting $A(s) = s^6 x(1/s)$, $B(s) = s^4 y(1/s)$, and $E(s) = s^9 W(1/s)$, which satisfy

$$
E^2 + 4 A^3 = s^2 B^4 + 8 s^{18}.
$$

Modulo the maximal ideal, $A$ starts with $a s^2$ ($a \in \{2, 4\}$), $B$ starts with $b s$ ($b \ne 0$), and $E$ is divisible by $s^3$. Since $\deg x = 6$ in characteristic zero, $A_0 \ne 0$. With $v(0) = +\infty$, set

$$
r = \min\left\{\frac{v(A_0)}{2},\, v(A_1),\, v(B_0),\, \frac{v(E_0)}{3},\, \frac{v(E_1)}{2},\, v(E_2)\right\} > 0.
$$

Pick $\mu$ of valuation $r$ in a further totally ramified extension, substitute $s = \mu T$, and divide $A, B, E$ by $\mu^2, \mu, \mu^3$, respectively. Every coefficient is integral, at least one lower coefficient survives by the choice of $r$, and $8s^{18}/\mu^6$ drops out modulo $\mu$, leaving

$$
e(T)^2 = T^2 (bT + w)^4 - 4(aT^2 + vT + u)^3.
$$

[SexticBoundary.lean](SexticBoundary.lean) proves $u = v = w = 0$ for all $a \in \{2, 4\}$ and $b \ne 0$ by evaluating the right-hand side at all five elements of $\mathbb{F}_5$ and at $\sqrt{2}, 2\sqrt{2}$ in $\mathbb{F}_{25}$ (where the norm of a square is a square). Independently, direct polynomial square-root tests rule out all $2 \cdot 4 \cdot (5^3 - 1) = 992$ cases with a surviving lower coefficient in $A$ or $B$. Once $u = v = w = 0$, $e(T)^2$ is a constant multiple of $T^6$, so $e$ is 0 or a multiple of $T^3$, contradicting the surviving lower coefficient.

## Remaining seeds

When $x(t_0) \equiv 3 \pmod 5$, the first reduction can have $\bar x = 3$ with $\bar z = 0$ or $\bar z = -\bar y^2$. Every reduction with nonconstant $\bar x$ is still excluded by the argument above, leaving only those two lines.

Independently, balancing at 13 restricts the marked triple to 116 of the 130 points of the surface over $\mathbb{F}_{13}$. Since 2 is not a cube modulo 13 and degrees below 6 are ruled out, $\bar x$ must have degree 6. Shift to kill the $T^5$ term and scale $T$ and $\bar x$ (by a cube root of unity) so the leading coefficient $\bar x_6$ is 1 or 2. Both factors have degree 9 and share the same leading coefficient (since $\deg \bar y \le 4$), whose square equals $-\bar x_6^3$, forcing $\bar x_6 = 1$. Factoring across all $13^5$ remaining choices of $\bar x$ yields 24 solutions (counted by divisor and leading scalar). Evaluating at every element of $\mathbb{F}_{13}$, both signs of $\bar y$, and all cube-root twists produces the 116 allowed seeds. This excludes $(1, 0, 1)$ at 13, while still allowing $(-2, 3, 1)$.

Run `uv run --with python-flint==0.9.0 SexticSearch.py --seeds-at-13` to reproduce both finite checks.

## The seed $(-2,3,1)$

At $(-2, 3, 1)$, shifting each degree-6 mod-13 solution to every parameter value hitting the mark (and restoring all cube-root twists and signs) always leaves $x'(0) \ne 0 \pmod{13}$. In any rational sextic map through this seed, the balancing radius at 13 must therefore be an integer, since the linear coefficient of $x$ becomes a 13-adic unit. A unique rational rescaling sets $x'(0) = 1$ while keeping all coefficients 13-integral, and after this normalization all mod-13 candidates collapse to a single triple.

Fixing the constant terms at $(-2, 3, 1)$ and $x_1 = 1$ leaves 18 unknowns ($x_2, \ldots, x_6$, $y_1, \ldots, y_4$, $z_1, \ldots, z_9$) and 18 equations from the nonconstant coefficients of $x^3 + zy^2 + z^2 - 2$. The Jacobian is invertible modulo 13, so the lift is unique. [SexticSearch.py](SexticSearch.py) lifts 699 times and checks the residual modulo $M = 13^{700}$.

For **each of the 18 coefficients**, if it is rational in lowest terms, the larger of its absolute numerator and positive denominator must exceed $10^{388}$. To prove this for a computed residue $r \bmod M$, the script finds two linearly independent integer pairs $(a_i, b_i)$ with $a_i \equiv r b_i \pmod M$ and $(|a_i| + |b_i|) 10^{388} < M$. Any rational $A/B$ of height at most $10^{388}$ matching $r \bmod M$ makes $a_i B - b_i A$ divisible by $M$ and strictly smaller than $M$ in absolute value, forcing both determinants to vanish and hence $(A, B) = (0, 0)$, a contradiction. The script checks all congruences, bounds, and independence exactly (in the coordinate normalized by $x'(0) = 1$).

Run `uv run --with python-flint==0.9.0 SexticSearch.py --exceptional-seed` to reproduce the marked lifts and height certificates.
