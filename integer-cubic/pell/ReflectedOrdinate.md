# The plane projection of a quartic Pell substitution

Consider a quartic rational chart on the Pell conic $u^2 - 3v^2 = 1$ mapping $(1, 0)$ to the seed $(0, 1, 1)$ on $z^2 + y^2 z + x^3 = 2$, with pole orders $4$, at most $3$, and at most $6$ for $x, y, z$ at the two conjugate ends at infinity. Completing the square in $z$ via $W = 2z + y^2$ puts the cubic surface equation in the form
$$
W^2 = y^4 + 8 - 4x^3.
$$
This note establishes two unconditional structural theorems for every such chart, with **no assumption on any second marked point**:

1. **No end-swapping reflection fixes $(x, y)$ and negates $W$:** Combining an exhaustive mod-$7$ census with two Lean-verified $7$-adic boundary certificates rules out every quartic chart admitting such a symmetry.
2. **Birational $(x, y)$-projection and a 15-monomial equation:** As a consequence, projecting the quartic curve to the $(x, y)$-plane is birational ($\mathbb{Q}(x, y) = \mathbb{Q}(u, v)$), and every candidate chart satisfies a unique linear relation among just **15** explicit monomials in $x, y, W$.

## Reduction to a one-variable identity over the quotient line

Suppose there is a rational reflection of $u^2 - 3v^2 = 1$ that swaps the two ends at infinity, fixes $x$ and $y$, and negates $W$.

Over $\mathbb{Q}(\sqrt{3})$, any reflection swapping the ends acts on the Laurent coordinate $\xi = u + \sqrt{3}\,v$ by $\xi \mapsto c/\xi$. Sums of opposite Laurent powers $\xi^j + (c/\xi)^j$ are polynomials in a single invariant linear coordinate $s$, while differences are an anti-invariant linear coordinate $r$ times polynomials in $s$. Both eigenspaces descend to $\mathbb{Q}$.

Write the invariant coordinate as $s = a(u - 1) + bv$. We must have $b \ne 0$: if $b = 0$, the reflection would fix the seed $(1, 0)$ while negating $W$, contradicting $W(1, 0) = 3$. Then
$$
r = u + \frac{3a}{b} v
$$
is anti-invariant with $r(1, 0) = 1$, and the two preimages of $s$ differ by the sign of $r$, because
$$
r^2 = 1 + \frac{6a}{b^2} s + \frac{3}{b^2} s^2.
$$

Writing $x = X(s)$, $y = Y(s)$, and $W = r E(s)$ reduces the surface equation to a one-variable polynomial identity
$$
4X^3 + Q E^2 = Y^4 + 8, \qquad Q(s) = 1 + As + 3B^2 s^2, \qquad B \ne 0,
$$
with $\deg X = 4$, $\deg Y \le 3$, $\deg E \le 5$, and $(X(0), Y(0), E(0)) = (0, 1, 3)$. Lean verifies the conic coordinate calculation in [ReflectedOrdinate.lean](ReflectedOrdinate.lean).

### Balancing at 7 and exhausting mod-7 reductions

Normalize the $7$-adic valuation by $v(7) = 1$, and let $h = \max(-v(c_i)/i)$ over all nonzero positive-degree coefficients of $X$ and $Y$. Pick $\lambda$ with $v(\lambda) = h$ in a totally ramified extension and substitute $s = \lambda T$:

* Both $X(\lambda T)$ and $Y(\lambda T)$ become $7$-integral, with at least one surviving nonconstant term.
* Because $Q$ and $E$ have unit constant terms ($1$ and $3$), their minimum coefficient valuations are at most $0$. Since $Q E^2 = Y^4 + 8 - 4X^3$ is integral, multiplicativity of the Gauss norm forces both $Q(\lambda T)$ and $E(\lambda T)$ to be integral as well.
* The quadratic coefficient $3(B\lambda)^2$ reduces modulo $7$ either to $0$ or to $3$ times a nonzero square.

[reflected_ordinate.py](reflected_ordinate.py) enumerates all pairs $(X, Y)$ over $\mathbb{F}_7[T]$ by their $4$ and $3$ nonconstant coefficients. For each pair, it pulls out the odd-multiplicity factors of $Y^4 + 8 - 4X^3$ as $Q$ (and when $Q$ could be a squared linear factor, tests every linear factor of the square root), fixing scalars by $Q(0) = 1$ and $E(0) = 3$.

Every surviving triple has a **nonzero** linear coefficient in $Q$. This forces $A \ne 0$, $v(A) = -h$, and therefore $h \in \mathbb{Z}$. Rescaling rationally via $s = T/A$ normalizes $Q_1 = 1$ exactly over $\mathbb{Q}$, leaving precisely **6** triples modulo $7$ (written in ascending degree):

| $X$ | $Y$ | $E$ | $Q$ |
| --- | --- | --- | --- |
| $aT^2$, $a = 1, 2, 4$ | $1 + 2T$ | $3 + T + 2T^2$ | $1 + T - T^2$ |
| $3T + 6T^2 + 5T^3$, $6T + 5T^2 + 3T^3$, or $5T + 3T^2 + 6T^3$ | $1 + T + 5T^2$ | $3 + 5T + T^2 + T^3 + 2T^4$ | $1 + T$ |

## Ruling out the two degenerations at infinity

Notice that in **both** rows of the table, $X$ drops degree modulo $7$ (to degree $2$ or $3$), even though $\deg X = 4$ over $\mathbb{Q}$. To expose the hidden high-degree coefficients that vanish modulo $7$, reverse all four polynomials by setting
$$
a(S) = S^4 X(1/S), \qquad d(S) = S^3 Y(1/S), \qquad c(S) = S^5 E(1/S), \qquad q(S) = S^2 Q(1/S).
$$
All four lie in $\mathbb{Z}_7[S]$ and satisfy
$$
4a^3 + q c^2 = d^4 + 8 S^{12}.
$$
In both cases below, take $v(0) = +\infty$ and index coefficients by powers of $S - \alpha$. Zooming in near $S = \alpha$ via a second valuation rescaling produces a boundary identity over $\mathbb{F}_7$ that forces every surviving term to vanish, yielding a contradiction.

### Case 1: First row of the table

1. **Mod-7 vanishing orders.** Modulo $7$, $a, d, c$ vanish at $S = 0$ to orders $2, 2, 3$ with leading coefficients $L \in \{1, 2, 4\}$, $2$, $2$, respectively, while $q(0) \equiv -1$.
2. **Centering at a critical point.** Because the reduced linear coefficient of $a'(S)$ is $2L \ne 0$, Hensel's lemma gives a root $\alpha$ of $a'$ in the maximal ideal, killing the linear coefficient ($a_1 = 0$).
3. **Second rescaling.** Set
   $$
   \rho = \min\left\{\frac{v(a_0)}{2},\, \frac{v(c_0)}{3},\, \frac{v(c_1)}{2},\, v(c_2),\, \frac{2v(d_0)}{3},\, 2v(d_1),\, 2v(\alpha)\right\}.
   $$
   Every entry is strictly positive, and $\rho$ is finite (otherwise $\alpha = a_0 = 0$, contradicting $\deg X = 4$). Pick $\mu$ with $v(\mu) = \rho$ and a square root $\sqrt{\mu}$ in a totally ramified extension (for instance, taking $\mu$ to be an even power of a uniformizer). Substitute $S = \alpha + \mu T$ and divide $a, c, d$ by $\mu^2, \mu^3, \mu^{3/2}$, respectively.
4. **Contradiction on the boundary.** Every rescaled polynomial is integral, higher-degree terms drop out upon reduction, and $8S^{12}/\mu^6$ reduces to $8R^{12}$ with $R = \overline{\alpha/\sqrt{\mu}}$. The reduced identity over $\mathbb{F}_7$ is
   $$
   4(LT^2 + A_0)^3 - (2T^3 + C_2 T^2 + C_1 T + C_0)^2 = (lT + m)^4 + 8R^{12}.
   $$
   The $T^5$ coefficient gives $C_2 = 0$, and Lean proves in [ReflectedOrdinate.lean](ReflectedOrdinate.lean) that the remaining five coefficients ($T^4$ down to $T^0$) force $A_0 = C_1 = C_0 = l = m = R = 0$, contradicting the minimality of $\rho$.

### Case 2: Second row of the table

1. **Mod-7 vanishing orders and centering.** Modulo $7$, $a, d, c, q$ all have simple zeros at $S = 0$. By Hensel's lemma, lift the simple zero of $a$ to a root $\alpha$ of $a$ in the maximal ideal.
2. **Second rescaling.** Set
   $$
   \rho = \min\left\{v(c_0),\, v(q_0),\, \frac{4v(d_0)}{3},\, 4v(\alpha)\right\}.
   $$
   This minimum is strictly positive and finite (if infinite, then $\alpha = 0$ and $q(0) = 0$, contradicting the nonzero $T^2$ coefficient $3(B/A)^2$ of $Q$). Pick $\mu$ of valuation $\rho$ with a fourth root $\mu^{1/4}$ in a totally ramified extension, substitute $S = \alpha + \mu T$, divide $a, c, q$ by $\mu$, and divide $d$ by $\mu^{3/4}$.
3. **Contradiction on the boundary.** Because $\bar q$ has linear coefficient $1$, the reduced identity over $\mathbb{F}_7$ becomes
   $$
   4(LT)^3 + (T + Q_0)(vT + C_0)^2 = D_0^4 + 8R^{12}, \qquad v \ne 0,
   $$
   where $R = \overline{\alpha/\mu^{1/4}}$. Matching coefficients of $T^2, T, 1$ over $\mathbb{F}_7$ forces $C_0 = Q_0 = D_0 = R = 0$, again contradicting the definition of $\rho$. Lean checks this boundary certificate in [ReflectedOrdinate.lean](ReflectedOrdinate.lean).

## Birational projection to the $(x, y)$-plane

Having ruled out end-swapping reflections, we can prove that the map $(u, v) \mapsto (x, y)$ is birational onto its image curve—with no assumption on any second marked point.

### Step 1: The chart itself is birational onto its curve on the cubic surface

Set $K = \mathbb{Q}(u, v)$ and $H = \mathbb{Q}(x, y, z)$, and suppose $k = [K : H] \ge 2$. By Lüroth's theorem, the normalization of the image curve is rational, and all poles of $x, y, z$ are images of the two original ends at infinity:

* If both ends map to the same point, that point is rational and $(x, y, z)$ becomes an ordinary polynomial family with $\deg x = 8/k \le 4$ passing through the integral seed, contradicting [OrdinaryPolynomial.md](OrdinaryPolynomial.md).
* If they map to distinct points, each has a single geometric preimage with ramification index $k$, producing conjugate quadratic points at infinity where $x$ has pole order $4/k \le 2$, contradicting [pole_two.md](pole_two.md).

Hence $H = K$.

### Step 2: Dropping $z$ preserves the function field

Since $W^2 = y^4 + 8 - 4x^3 \in \mathbb{Q}(x, y)$, the projection to the $(x, y)$-plane has degree $1$ or $2$. Suppose for contradiction that the degree is $2$. Then the covering involution fixes $x$ and $y$, negates $W$, and permutes the two poles of $x$:

* Swapping the two ends was ruled out in the previous section.
* Fixing both ends acts on the split torus by $\xi \mapsto -\xi$, which forces the invariant function $y$ to have even pole order (at most $2$) and the anti-invariant function $W$ to have odd pole order. That contradicts $W^2 = y^4 + 8 - 4x^3$, which gives $W$ pole order $6$.

Therefore $\mathbb{Q}(x, y) = \mathbb{Q}(u, v)$.

## A fifteen-coefficient implicit equation

Birationality lets us pin down the exact shape of the equation cutting out the chart's image on the cubic surface. Assign weights $(4, 3, 6)$ to $(x, y, W)$.

1. **Weighted degree of the plane curve.** As a map to $\mathbb{P}^1$, $x$ has degree $8$, and $y$ has no poles over finite $x$, so $y$ is integral over $\mathbb{Q}[x]$. Its irreducible plane equation $G(x, y) = 0$ can therefore be taken monic of degree $8$ in $y$. Because the projection is birational, the eight conjugates of $y$ over $\mathbb{Q}(x)$ are its eight branches above a generic $x$. Near $x = \infty$, each branch grows at most like $x^{3/4}$ (pole order $4$ for $x$, at most $3$ for $y$), so the coefficient of $y^j$ in $G$ has degree at most $\lfloor 3(8 - j)/4 \rfloor$ in $x$. Thus $G$ has weighted degree $24$.
2. **Cutting out $C$ by a quartic on the cubic surface.** Let $C$ be the projective image on the smooth cubic surface $S$ and $H$ the hyperplane class. In [QuarticGeometry.md](QuarticGeometry.md) we showed $C \cdot \ell = 4$ for all $27$ geometric lines $\ell \subset S$. Because the $27$ lines generate the geometric Picard group with a nondegenerate intersection form (via the blowup of $\mathbb{P}^2$ at six points; see [Picard group of a cubic surface](https://pmc.ncbi.nlm.nih.gov/articles/PMC7340950/)), this forces $C \sim 4H$. Both $C$ and $4H$ are defined over $\mathbb{Q}$, so the $1$-dimensional space of sections cutting out $C$ descends to $\mathbb{Q}$. By the hypersurface exact sequence, a section of $\mathcal{O}_S(4)$ restricts from an ambient quartic, so in the affine coordinate ring of $S$, $C$ is cut out with multiplicity $1$ by a polynomial reducing to $U(x, y) + V(x, y)W$.
3. **Comparing norms and weighted degrees.** Taking the norm under $W \mapsto -W$ produces a nonzero constant multiple of $G$: its only zero divisor on the $(x, y)$-plane is the projected curve, with multiplicity $1$ because the projection is birational and generically unramified there (and $C$ differs from its conjugate since $W = 3 \ne 0$ at the seed). Hence
   $$
   cG = U^2 - (y^4 + 8 - 4x^3) V^2.
   $$
   The weighted leading terms on the right cannot cancel, because $y^4 - 4x^3$ has odd degree in $x$ and is not a square in $\mathbb{Q}(x, y)$. Consequently,
   $$
   \deg_{\mathrm{wt}} U \le 12, \qquad \deg_{\mathrm{wt}} V \le 6.
   $$

**Consequence:** Every candidate chart satisfies a linear relation among just **15 monomials**—the $11$ monomials $x^i y^j$ with $4i + 3j \le 12$, plus the $4$ monomials $W, Wy, Wy^2, Wx$. Up to scaling, this relation is **unique**: any second relation within those weight bounds is a multiple in the affine coordinate ring, and the norm of the multiplier has weighted degree $0$, forcing it to be constant by the same leading-term argument.

For a chart with numerators $X, Y, Z$ and denominator $L = 1 - 3t^2$, each of the $15$ columns is the polynomial
$$
X^i Y^j (2Z + Y^2)^k L^{12 - 4i - 3j - 6k}.
$$
Modulo $7$, [reflected_ordinate.py](reflected_ordinate.py) checks that this matrix has rank $14$ on $2$ of the $12$ full-pole orbits and rank $10$ on the other $10$, so all $12$ mod-$7$ orbits pass this necessary condition.
