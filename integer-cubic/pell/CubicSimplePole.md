# A local obstruction at a simple Pell denominator root

Suppose we have a cubic Pell substitution $X^3 + ZY^2 + Z^2 L^3 = 2L^9$ whose reduction modulo a prime $p \notin \{2, 3\}$ behaves deceptively at a simple root $\alpha$ of the denominator $L$: $Z(\alpha)$ stays a unit modulo $p$, while $Y$ has a double root at $\alpha$ modulo $p$ ($Y(\alpha) \equiv Y'(\alpha) \equiv 0$). One might expect that $Y(\alpha)$ and $Y'(\alpha)$ are merely divisible by $p$, allowing $X(\alpha)$ to remain nonzero in characteristic zero.

This note proves that **the opposite happens**: the cubic surface equation forces $Y(\alpha)$, $Y'(\alpha)$, and $X(\alpha)$ to vanish **exactly** in characteristic zero. On an irreducible Pell denominator $L = 1 - Dt^2$, $X(\alpha) = 0$ forces $L \mid X$ globally, collapsing the pole order of $x = X/L^3$ to at most $2$ — where [pole_two.md](pole_two.md) already forces the entire family to be constant.

## The local vanishing theorem

> **Theorem.** Let $F$ be a discretely valued field whose residue field $k$ does not have characteristic $2$ or $3$. Suppose $X, Y, Z, L \in \mathcal{O}_F[t]$ have integral coefficients and satisfy
>
> $$
> X^3 + ZY^2 + Z^2 L^3 = 2 L^9.
> $$
>
> Suppose $\alpha \in \mathcal{O}_F$ is an integral root of $L$ with $L'(\alpha)$ a unit. If $Z(\alpha)$ is a unit and both $Y(\alpha)$ and $Y'(\alpha)$ vanish in $k$, then
>
> $$
> Y(\alpha) = Y'(\alpha) = X(\alpha) = 0 \qquad \text{in } F.
> $$

### Proof: weighted zoom and parity contradiction

**The big idea:** Expand around $\alpha$ in $s = t - \alpha$. If either $Y(\alpha)$ or $Y'(\alpha)$ is nonzero, we zoom in at the exact scale $s = \lambda^2 T$ where $X^3$, $ZY^2$, and $Z^2 L^3$ all scale by $\lambda^6$ while $2L^9$ acquires $\lambda^{18}$ and vanishes modulo the maximal ideal. The reduced polynomial $b(T)$ coming from $Y$ is nonzero of degree at most $1$. Pulling back by $T = w^2/k_1$ maps into the smooth elliptic curve $x^3 + ey^2 = -e^2$, forcing $b(w^2/k_1)$ to be a scalar multiple of $w^3$ — impossible because $b(w^2/k_1)$ contains only **even** powers of $w$!

Now for the exact details:

1. **Choose the zoom scale:** Expand $Y(\alpha + s) = B_0 + B_1 s + B_2 s^2 + \cdots$. By hypothesis, $v(B_0) > 0$ and $v(B_1) > 0$. Suppose for contradiction that $B_0$ or $B_1$ is nonzero, and define (with $v(0) = +\infty$)

   $$
   r = \min\left(\frac{v(B_0)}{3},\, v(B_1)\right) > 0.
   $$

   Adjoin a root of a uniformizer in a totally ramified extension to obtain an element $\lambda$ with $v(\lambda) = r$.
2. **Rescale by $\lambda$:** Substitute $s = \lambda^2 T$ and define

   $$
   a_1 = \lambda^{-2} X(\alpha + \lambda^2 T), \qquad
   b_1 = \lambda^{-3} Y(\alpha + \lambda^2 T), \qquad
   E = Z(\alpha + \lambda^2 T), \qquad
   L_1 = \lambda^{-2} L(\alpha + \lambda^2 T).
   $$

   Check each term's integrality and reduction modulo the maximal ideal:
   * $b_1(T) = B_0 \lambda^{-3} + B_1 \lambda^{-1} T + B_2 \lambda T^2 + \cdots$. By the choice of $r$, both $B_0 \lambda^{-3}$ and $B_1 \lambda^{-1}$ are integral and at least one is a unit, while every term of degree $\ge 2$ carries a strictly positive power of $\lambda$ and drops out on reduction. Hence $b_1$ reduces to a **nonzero** polynomial $b(T)$ of degree at most $1$.
   * $E$ reduces to the nonzero constant $e = \overline{Z(\alpha)} \ne 0$.
   * Because $L(\alpha) = 0$ and $L'(\alpha)$ is a unit, $L_1$ reduces to $k_1 T$ with $k_1 = \overline{L'(\alpha)} \ne 0$.
3. **Cube integrality and the reduced equation:** Dividing $X^3 + ZY^2 + Z^2 L^3 = 2L^9$ by $\lambda^6$ gives

   $$
   a_1^3 + E b_1^2 + E^2 L_1^3 = 2 \lambda^{12} L_1^9.
   $$

   This writes $a_1^3$ as an integral polynomial, which forces $a_1$ itself to be integral. Reducing modulo the maximal ideal (where $2\lambda^{12} L_1^9$ vanishes since $v(\lambda^{12}) = 12r > 0$) yields

   $$
   a^3 + eb^2 + e^2(k_1 T)^3 = 0.
   $$

4. **Constant-fiber parity contradiction:** Substitute $T = w^2/k_1$, so $(k_1 T)^3 = w^6$. Dividing by $w^6$ shows that

   $$
   x = \frac{a(w^2/k_1)}{w^2}, \qquad y = \frac{b(w^2/k_1)}{w^3}
   $$

   solve the smooth cubic curve $x^3 + ey^2 = -e^2$ in $k(w)$. By the polynomial Fermat–Catalan theorem in characteristic not $2$ or $3$, this curve has only **constant** points over $k(w)$. Hence $b(w^2/k_1)$ must be a scalar multiple of $w^3$. Because $b(w^2/k_1)$ has only **even** powers of $w$ (namely $1$ and $w^2$), that scalar must be $0$, forcing $b = 0$ — contradicting step 2.

This proves $B_0 = B_1 = 0$, i.e., $Y(\alpha) = Y'(\alpha) = 0$. Plugging $t = \alpha$ into $X^3 + ZY^2 + Z^2 L^3 = 2L^9$ (with $L(\alpha) = Y(\alpha) = 0$) immediately gives $X(\alpha) = 0$.

* **Verification split:** The written proof above constructs $\lambda$ and computes the reduced coefficients, while Lean verifies the local obstruction in [CubicSimplePole.lean](CubicSimplePole.lean), cube integrality in [CubicAnnulus.lean](CubicAnnulus.lean), and the constant-fiber theorem in [PellConstantFiber.lean](PellConstantFiber.lean).

## Application: the split residue classes through $(0,1,1)$

Over $\mathbb{F}_{13}$, the split Pell denominator $L = 1 - 3t^2$ has simple roots at $t = 3$ and $t = -3$ (since $3 \cdot 3^2 = 27 \equiv 1 \pmod{13}$). Modulo the seed-preserving symmetries $t \mapsto \pm t$ and $x \mapsto \zeta x$ ($\zeta^3 = 1$), [cubic_seed13.py](cubic_seed13.py) runs an exhaustive divisor search over all $804{,}835$ normalized abscissas $X$: for each $X$, it factors $2L^9 - X^3$, tests every divisor $Z$ of degree at most $6$ with $Z(0) = 1$, and checks whether $(2L^9 - X^3)/Z - ZL^3$ is a square matching $Y(0) = 1$.

The search finds one constant model and **two** nonconstant representatives. The table records the vanishing orders of $(X, Y, Z)$ at the two simple roots $3$ and $-3$, together with $Z(-3)$:

| Representative | Orders at $3$ | Orders at $-3$ | $Z(-3)$ |
| --- | ---: | ---: | ---: |
| 1 | $(1, 2, 0)$ | $(1, 2, 0)$ | 1 |
| 2 | $(2, 0, 6)$ | $(1, 3, 0)$ | 12 |

Both representatives satisfy the hypotheses of our local theorem at $\alpha \equiv -3 \pmod{13}$: $Y$ vanishes to order at least $2$ and $Z(-3) \not\equiv 0$. Negating $t$ merely swaps the two roots, and twisting $X$ by a cube root of unity leaves the vanishing orders and $Z(-3)$ unchanged. [CubicSimplePole.lean](CubicSimplePole.lean) verifies the required values and first derivatives for both representatives directly.

### Global descent to pole order $\le 2$

Now let $D \in \mathbb{Q}^\times$ be nonsquare over $\mathbb{Q}$ yet a square in $\mathbb{Q}_{13}$.

1. **Normalize locally at $13$:** Replacing $t$ by $\sqrt{3/D}\,t$ over $\mathbb{Q}_{13}$ turns the denominator $1 - Dt^2$ into $1 - 3t^2$ while fixing the mark $t = 0$. As proved in [CubicPellAt13.md](CubicPellAt13.md), the cubic numerators in this coordinate are $13$-integral and have a nonconstant reduction modulo $13$, so their reduction falls into one of the two orbits above.
2. **Lift the root and apply the local theorem:** By Hensel's lemma, the simple residue root $-3 \in \mathbb{F}_{13}$ (or $3$ after sign flip) lifts to an exact root $\alpha \in \mathbb{Q}_{13}$ of $1 - 3t^2$. Our local theorem forces $X(\alpha) = 0$.
3. **Drop the pole order globally:** Undoing the local scaling shows that the original rational numerator vanishes at a root of $1 - Dt^2$. Because $1 - Dt^2$ is irreducible over $\mathbb{Q}$, it divides the numerator globally in $\mathbb{Q}[t]$, cancelling one power of $1 - Dt^2$ and dropping the pole order of $x = X/(1 - Dt^2)^3$ to at most $2$. The pole-order-$2$ theorem in [pole_two.md](pole_two.md) then forces the entire family to be constant.

The exact same local proof works over $\mathbb{F}_{169}$ after splitting an unramified nonsquare unit denominator at $13$, because our theorem allows any unit $e$ and any simple root with nonzero derivative. Both the nonsplit enumeration and the opposite orientation of $z$ are assembled into the complete argument in [CubicPellAt13.md](CubicPellAt13.md).
