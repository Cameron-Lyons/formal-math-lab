# A local obstruction at a simple Pell denominator root

Let $F$ be a discretely valued field whose residue field $k$ does not have characteristic 2 or 3. Suppose $X, Y, Z, L$ have integral coefficients and satisfy

$$
X^3 + ZY^2 + Z^2 L^3 = 2 L^9.
$$

Suppose $\alpha$ is an integral root of $L$ with $L'(\alpha)$ a unit. If $Z(\alpha)$ is a unit and both $Y(\alpha)$ and $Y'(\alpha)$ vanish in $k$, then

$$
Y(\alpha) = Y'(\alpha) = X(\alpha) = 0 \qquad \text{in } F.
$$

To prove this, expand $Y(\alpha + s) = B_0 + B_1 s + \cdots$. Suppose for contradiction that $B_0$ or $B_1$ is nonzero, and put $r = \min(v(B_0)/3, v(B_1)) > 0$ (with $v(0) = +\infty$). Adjoin a root of a uniformizer in a totally ramified extension to pick an element $\lambda$ of valuation $r$. Substitute $s = \lambda^2 T$ and define

$$
a_1 = \lambda^{-2} X(\alpha + \lambda^2 T), \quad
b_1 = \lambda^{-3} Y(\alpha + \lambda^2 T), \quad
E = Z(\alpha + \lambda^2 T), \quad
L_1 = \lambda^{-2} L(\alpha + \lambda^2 T).
$$

By our choice of $r$, $b_1$ is integral with nonzero reduction $b$, and every term of $b_1$ of degree above 1 drops out on reduction. Meanwhile $E$ reduces to $e = \overline{Z(\alpha)} \ne 0$, and $L_1$ reduces to $k_1 T$ with $k_1 = \overline{L'(\alpha)} \ne 0$.

Dividing the original equation by $\lambda^6$ writes $a_1^3$ as an integral polynomial, so $a_1$ is integral too. Its reduction $a$ satisfies

$$
a^3 + eb^2 + e^2(k_1 T)^3 = 0.
$$

Now set $T = w^2/k_1$. Then $x = a(w^2/k_1)/w^2$ and $y = b(w^2/k_1)/w^3$ solve $x^3 + ey^2 = -e^2$. By the polynomial Fermat-Catalan theorem in characteristic not 2 or 3, this smooth cubic has only constant points over $k(w)$. Hence $b(w^2/k_1)$ is a scalar multiple of $w^3$. Because $b(w^2/k_1)$ has only even powers of $w$, that scalar must be 0, giving $b = 0$ and a contradiction.

This proves $B_0 = B_1 = 0$, and plugging $\alpha$ into the original equation gives $X(\alpha) = 0$. The written proof above chooses $\lambda$ and computes the reduced coefficients, while Lean verifies the local obstruction in [CubicSimplePole.lean](CubicSimplePole.lean), cube integrality in [CubicAnnulus.lean](CubicAnnulus.lean), and the constant-fiber theorem in [PellConstantFiber.lean](PellConstantFiber.lean).

## The split residue classes through $(0,1,1)$

Over $\mathbb{F}_{13}$, the denominator $L = 1 - 3t^2$ has simple roots at $3$ and $-3$. Using the symmetries $t \mapsto \pm t$ and $x \mapsto \zeta x$ ($\zeta^3 = 1$), [cubic_seed13.py](cubic_seed13.py) runs an exhaustive divisor search over all 804,835 normalized abscissas $X$. For each $X$, it factors $2L^9 - X^3$, tests every divisor $Z$ of degree at most 6 with $Z(0) = 1$, and checks whether $(2L^9 - X^3)/Z - ZL^3$ is a square matching $Y(0) = 1$.

The search finds one constant model and two nonconstant representatives. The table gives the vanishing orders of $(X, Y, Z)$ at $3$ and $-3$:

| Representative | Orders at $3$ | Orders at $-3$ | $Z(-3)$ |
| --- | ---: | ---: | ---: |
| 1 | $(1, 2, 0)$ | $(1, 2, 0)$ | 1 |
| 2 | $(2, 0, 6)$ | $(1, 3, 0)$ | 12 |

Both representatives satisfy the local criterion at $-3$. Negating $t$ swaps the two roots, and twisting $X$ by a cube root of unity does not change the orders or $Z(-3)$. [CubicSimplePole.lean](CubicSimplePole.lean) checks the required values and first derivatives for both representatives.

Now let $D \in \mathbb{Q}^\times$ be nonsquare over $\mathbb{Q}$ and a square in $\mathbb{Q}_{13}$. Replacing $t$ by $\sqrt{3/D}\,t$ turns the local denominator into $1 - 3t^2$ while fixing $t = 0$. As shown in [CubicPellAt13.md](CubicPellAt13.md), the cubic numerators in this coordinate are integral and have a nonconstant reduction. Hensel's lemma lifts the simple residue root to $\alpha \in \mathbb{Q}_{13}$. By our local theorem, $X(\alpha) = 0$, so the original rational numerator vanishes at a root of $1 - Dt^2$. Because $1 - Dt^2$ is irreducible over $\mathbb{Q}$, it divides the numerator globally, dropping the pole order of $x = X/(1 - Dt^2)^3$ to at most 2. The pole-order-2 theorem in [pole_two.md](pole_two.md) then forces the family to be constant.

The same local proof works over $\mathbb{F}_{169}$ after splitting an unramified nonsquare unit denominator at 13, because it allows any unit $e$ and any simple root with nonzero derivative. Both the nonsplit enumeration and the opposite orientation of $z$ are included in the full argument in [CubicPellAt13.md](CubicPellAt13.md).
