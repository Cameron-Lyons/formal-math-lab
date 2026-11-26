# The plane projection of a quartic Pell substitution

Consider a quartic chart on $u^2 - 3v^2 = 1$ sending $(1, 0)$ to $(0, 1, 1)$, with pole orders $4$, at most $3$, and at most $6$ for $x, y, z$ at the two conjugate ends. Put $W = 2z + y^2$, so $W^2 = y^4 + 8 - 4x^3$. **There is no rational reflection of the conic that swaps the two ends, fixes $x$ and $y$, and negates $W$.** No condition is placed on any second marked point.

## Reduction over the quotient line

Over $\mathbb{Q}(\sqrt{3})$, any reflection swapping the ends acts on the Laurent coordinate $\xi = u + \sqrt{3}\,v$ by $\xi \mapsto c/\xi$. Sums of opposite Laurent powers $\xi^j + (c/\xi)^j$ are polynomials in an invariant linear coordinate, and differences are an anti-invariant linear coordinate times polynomials in that same invariant coordinate. Both eigenspaces descend to $\mathbb{Q}$.

Write the invariant coordinate as $s = a(u - 1) + bv$. We must have $b \ne 0$, since $b = 0$ fixes the seed $(1, 0)$, contradicting $W(1, 0) = 3$. Then $r = u + (3a/b)v$ is anti-invariant with $r(1, 0) = 1$, and the two preimages of $s$ differ by the sign of $r$, because

$$
r^2 = 1 + \frac{6a}{b^2} s + \frac{3}{b^2} s^2.
$$

Any chart with this reflection symmetry therefore gives a one-variable identity

$$
4X^3 + QE^2 = Y^4 + 8, \qquad Q = 1 + As + 3B^2 s^2, \qquad B \ne 0,
$$

with $\deg X = 4$, $\deg Y \le 3$, $\deg E \le 5$, and $(X, Y, E)(0) = (0, 1, 3)$ (from $W = rE(s)$). Lean verifies the conic coordinate calculation in [ReflectedOrdinate.lean](ReflectedOrdinate.lean).

Now normalize the 7-adic valuation by $v(7) = 1$, and let $h = \max(-v(c_i)/i)$ over all nonzero positive-degree coefficients of $X$ and $Y$. Pick $\lambda$ of valuation $h$ in a totally ramified extension and substitute $s = \lambda T$. Both rescaled polynomials become integral with at least one surviving nonconstant term. Since $Q$ and $E$ have unit constant terms, their minimum coefficient valuations are at most 0; because $QE^2 = Y^4 + 8 - 4X^3$ is integral, multiplicativity of the Gauss norm forces both $Q$ and $E$ to be integral. The quadratic coefficient $3(B\lambda)^2$ reduces modulo 7 either to 0 or to 3 times a nonzero square.

[reflected_ordinate.py](reflected_ordinate.py) enumerates all choices of $X$ and $Y$ over $\mathbb{F}_7$ by their 4 and 3 nonconstant coefficients. For each pair, it pulls out the odd-multiplicity factors of $Y^4 + 8 - 4X^3$ to form $Q$ (and when $Q$ could be a squared linear factor, tests every linear factor of the square root), fixing scalars by $Q(0) = 1$ and $E(0) = 3$. Every surviving triple has a nonzero linear coefficient in $Q$. Thus $A \ne 0$, $v(A) = -h$, and $h$ is an integer. Substituting $s = T/A$ over $\mathbb{Q}$ normalizes $Q_1 = 1$ exactly, leaving precisely 6 triples modulo 7 (written in ascending degree):

| $X$ | $Y$ | $E$ | $Q$ |
| --- | --- | --- | --- |
| $aT^2$, $a = 1, 2, 4$ | $1 + 2T$ | $3 + T + 2T^2$ | $1 + T - T^2$ |
| $3T + 6T^2 + 5T^3$, $6T + 5T^2 + 3T^3$, or $5T + 3T^2 + 6T^3$ | $1 + T + 5T^2$ | $3 + 5T + T^2 + T^3 + 2T^4$ | $1 + T$ |

## The two possible degenerations at infinity

Reverse the four polynomials by setting $a = S^4 X(1/S)$, $d = S^3 Y(1/S)$, $c = S^5 E(1/S)$, and $q = S^2 Q(1/S)$. All four lie in $\mathbb{Z}_7[S]$ and satisfy

$$
4a^3 + qc^2 = d^4 + 8S^{12}.
$$

In both cases below, take $v(0) = +\infty$ and index coefficients by powers of $S - \alpha$.

### First row of the table

Modulo 7, $a, d, c$ vanish at $S = 0$ to orders $2, 2, 3$ with leading coefficients $L \in \{1, 2, 4\}$, $2$, $2$, and $q(0) \equiv -1$. Since the reduced linear coefficient of $a'$ is $2L \ne 0$, Hensel's lemma gives a root $\alpha$ of $a'$ in the maximal ideal, so $a_1 = 0$. Put

$$
\rho = \min\left\{\frac{v(a_0)}{2},\, \frac{v(c_0)}{3},\, \frac{v(c_1)}{2},\, v(c_2),\, \frac{2v(d_0)}{3},\, 2v(d_1),\, 2v(\alpha)\right\}.
$$

Every entry is positive, and $\rho$ is finite (otherwise $\alpha = a_0 = 0$, contradicting $\deg X = 4$). Pick $\mu$ with $v(\mu) = \rho$ and a square root $\sqrt{\mu}$ in a totally ramified extension (for instance, taking $\mu$ to be an even power of a uniformizer). Substitute $S = \alpha + \mu T$ and divide $a, c, d$ by $\mu^2, \mu^3, \mu^{3/2}$, respectively. Every rescaled polynomial is integral, higher terms disappear on reduction, and $8S^{12}/\mu^6$ reduces to $8R^{12}$ with $R = \overline{\alpha/\sqrt{\mu}}$. The reduced identity is

$$
4(LT^2 + A_0)^3 - (2T^3 + C_2 T^2 + C_1 T + C_0)^2 = (lT + m)^4 + 8R^{12}.
$$

The $T^5$ coefficient gives $C_2 = 0$, and Lean checks in [ReflectedOrdinate.lean](ReflectedOrdinate.lean) that the remaining five coefficients from $T^4$ down to $T^0$ force $A_0 = C_1 = C_0 = l = m = R = 0$, contradicting the minimum $\rho$.

### Second row of the table

Modulo 7, $a, d, c, q$ all have simple zeros at $S = 0$. Lift the zero of $a$ to a root $\alpha$ in the maximal ideal, and set

$$
\rho = \min\left\{v(c_0),\, v(q_0),\, \frac{4v(d_0)}{3},\, 4v(\alpha)\right\}.
$$

This minimum is positive and finite (if infinite, $\alpha = 0$ and $q(0) = 0$, contradicting the nonzero $T^2$ coefficient $3(B/A)^2$ of $Q$). Pick $\mu$ of valuation $\rho$ with a fourth root in a totally ramified extension, substitute $S = \alpha + \mu T$, divide $a, c, q$ by $\mu$, and divide $d$ by $\mu^{3/4}$. Because $\bar q$ has linear coefficient 1, the residue identity becomes

$$
4(LT)^3 + (T + Q_0)(vT + C_0)^2 = D_0^4 + 8R^{12}, \qquad v \ne 0,
$$

where $R = \overline{\alpha/\mu^{1/4}}$. Matching coefficients of $T^2, T, 1$ over $\mathbb{F}_7$ forces $C_0 = Q_0 = D_0 = R = 0$, again contradicting the minimum $\rho$. Lean checks this boundary certificate in [ReflectedOrdinate.lean](ReflectedOrdinate.lean).

## Birational projection

Set $K = \mathbb{Q}(u, v)$ and $H = \mathbb{Q}(x, y, z)$, and suppose $k = [K : H] \ge 2$. By Lüroth's theorem, the normalization of the image curve is rational, and all poles of $x, y, z$ are images of the two original ends.

* If both ends map to the same point, that point is rational and $(x, y, z)$ becomes an ordinary polynomial family with $\deg x = 8/k \le 4$ through the integral seed, contradicting [OrdinaryPolynomial.md](OrdinaryPolynomial.md).
* If they map to distinct points, each has a single geometric preimage with ramification index $k$, giving conjugate quadratic points at infinity where $x$ has pole order $4/k \le 2$, contradicting [pole_two.md](pole_two.md).

Therefore $H = K$. Since $W^2 \in \mathbb{Q}(x, y)$, projecting to the $(x, y)$-plane has degree 1 or 2. In degree 2, the covering involution fixes $x, y$, negates $W$, and permutes the two poles of $x$. We just ruled out swapping the two ends. An involution fixing both ends acts on the split torus by $\xi \mapsto -\xi$, which forces $y$ to have even pole order at most 2 and the anti-invariant $W$ to have odd pole order. That contradicts $W^2 = y^4 + 8 - 4x^3$, which gives $W$ pole order 6. Hence $\mathbb{Q}(x, y) = \mathbb{Q}(u, v)$, with no assumption on any second marked point.

## A fifteen-coefficient implicit equation

Assign weights $4, 3, 6$ to $x, y, W$. Since $x$ has degree 8 as a map to $\mathbb{P}^1$ and $y$ has no poles over finite $x$, $y$ is integral over $\mathbb{Q}[x]$, so the irreducible plane equation $G(x, y) = 0$ can be taken monic of degree 8 in $y$. Because the projection is birational, the eight conjugates of $y$ over $\mathbb{Q}(x)$ are its eight branches above a generic $x$. Near $x = \infty$, each branch grows at most like $x^{3/4}$ (pole order 4 for $x$, at most 3 for $y$), so the coefficient of $y^j$ in $G$ has degree at most $\lfloor 3(8 - j)/4 \rfloor$ in $x$. Thus $G$ has weighted degree 24.

Let $C$ be the projective image on the smooth cubic surface $S$ and $H$ the hyperplane class. In [QuarticGeometry.md](QuarticGeometry.md) we showed $C \cdot \ell = 4$ for all 27 geometric lines. Since the 27 lines generate the geometric Picard group with a nondegenerate intersection form (via the blowup of $\mathbb{P}^2$ at six points; see [Picard group of a cubic surface](https://pmc.ncbi.nlm.nih.gov/articles/PMC7340950/)), this forces $C \sim 4H$. Both $C$ and $4H$ are defined over $\mathbb{Q}$, so the 1-dimensional space of sections cutting out $C$ descends to $\mathbb{Q}$. By the hypersurface exact sequence, a section of $\mathcal{O}_S(4)$ restricts from an ambient quartic, so in the affine coordinate ring of $S$, $C$ is cut out with multiplicity 1 by a polynomial reducing to $U(x, y) + V(x, y)W$.

Taking the norm under $W \mapsto -W$ gives a nonzero constant multiple of $G$: its only zero divisor on the $(x, y)$-plane is the projected curve, with multiplicity 1 because the projection is birational and generically unramified there (and $C$ differs from its conjugate since $W = 3 \ne 0$ at the seed). Hence

$$
cG = U^2 - (y^4 + 8 - 4x^3) V^2.
$$

The weighted leading terms cannot cancel, because $y^4 - 4x^3$ has odd degree in $x$ and is not a square in $\mathbb{Q}(x, y)$. Therefore $\deg_{\mathrm{wt}} U \le 12$ and $\deg_{\mathrm{wt}} V \le 6$. **Every candidate chart satisfies a linear relation among just 15 monomials:** the 11 monomials $x^i y^j$ with $4i + 3j \le 12$, plus $W, Wy, Wy^2, Wx$. Up to scaling, this relation is unique: any second relation within those weight bounds is a multiple in the affine coordinate ring, and the norm of the multiplier has weighted degree 0, forcing it to be constant by the same leading-term argument.

For a chart with numerators $X, Y, Z$ and denominator $L = 1 - 3t^2$, each of the 15 columns is the polynomial

$$
X^i Y^j (2Z + Y^2)^k L^{12 - 4i - 3j - 6k}.
$$

Modulo 7, [reflected_ordinate.py](reflected_ordinate.py) checks that this matrix has rank 14 on 2 of the 12 full-pole orbits and rank 10 on the other 10, so all 12 orbits pass this necessary condition.
