# A local obstruction at a simple Pell denominator root

Let $F$ be a discretely valued field with residue field $k$ of characteristic different from 2 and 3. Let $X,Y,Z,L$ have integral coefficients and satisfy
$$
X^3+ZY^2+Z^2L^3=2L^9.
$$
Suppose $\alpha$ is an integral root of $L$ with $L'(\alpha)$ a unit. If $Z(\alpha)$ is a unit and $Y(\alpha),Y'(\alpha)$ vanish in $k$, then
$$
Y(\alpha)=Y'(\alpha)=X(\alpha)=0\qquad\text{in }F.
$$

Indeed, write $Y(\alpha+s)=B_0+B_1s+\cdots$. If $B_0$ or $B_1$ is nonzero, put $r=\min(v(B_0)/3,v(B_1))>0$, with $v(0)=+\infty$. Adjoin a suitable root of a uniformizer in a totally ramified extension, and choose $\lambda$ of valuation $r$. With $s=\lambda^2 T$, form
$$
a_1=\lambda^{-2}X(\alpha+\lambda^2T),\quad
b_1=\lambda^{-3}Y(\alpha+\lambda^2T),\quad
E=Z(\alpha+\lambda^2T),\quad
L_1=\lambda^{-2}L(\alpha+\lambda^2T).
$$
The minimum makes $b_1$ integral and ensures that its reduction $b$ is nonzero. Every term of $b_1$ above degree one disappears on reduction. The reductions of $E,L_1$ are $e=\overline{Z(\alpha)}\ne0$ and $k_1T$ with $k_1=\overline{L'(\alpha)}\ne0$. Dividing the original equation by $\lambda^6$ expresses $a_1^3$ as an integral polynomial. Hence $a_1$ is integral. Its reduction $a$ satisfies
$$
a^3+eb^2+e^2(k_1T)^3=0.
$$
Substitute $T=w^2/k_1$. Then $x=a(w^2/k_1)/w^2$ and $y=b(w^2/k_1)/w^3$ satisfy $x^3+ey^2=-e^2$. This nonsingular cubic admits only constant points over $k(w)$, by the polynomial Fermat–Catalan theorem in characteristic different from 2 and 3. Therefore $b(w^2/k_1)$ is a scalar multiple of $w^3$. Its odd-degree coefficients vanish, so this multiple is zero and $b=0$, a contradiction. This proves $B_0=B_1=0$. Substitution of $\alpha$ in the original equation yields $X(\alpha)=0$. Lean checks polynomial cube integrality, specialization of the scaled identity and the contradiction over the residue field. The selection of the scaling element and the reduced coefficients are given above. [Local obstruction](CubicSimplePole.lean) · [Cube integrality](CubicAnnulus.lean) · [Constant-fiber theorem](PellConstantFiber.lean)

## The split residue classes through $(0,1,1)$

For $L=1-3t^2$ over $\mathbb F_{13}$, the roots $3,-3$ are simple. An independent divisor search over all 804,835 abscissa representatives found one constant model and two nonconstant representatives. The actions on the abscissa are $t\mapsto\pm t$ and $x\mapsto\zeta x$, where $\zeta^3=1$. For each abscissa $X$ the search factors $2L^9-X^3$, enumerates every divisor $Z$ of degree at most six with $Z(0)=1$ and checks if $(2L^9-X^3)/Z-ZL^3$ is a square with the prescribed ordinate at zero. The three orders in the table refer to the numerators $X,Y,Z$. [Exhaustive residue checker](cubic_seed13.py)

| Representative | Orders at $3$ | Orders at $-3$ | $Z(-3)$ |
|---|---:|---:|---:|
| 1 | $(1,2,0)$ | $(1,2,0)$ | 1 |
| 2 | $(2,0,6)$ | $(1,3,0)$ | 12 |

Both representatives meet the criterion at $-3$. Changing $t$ to $-t$ exchanges the two ends. Multiplying $X$ by a cube root of unity leaves the criterion unchanged. Lean checks the requisite values and first derivatives for the two displayed representatives. [Split residue certificate](CubicSimplePole.lean)

Suppose now that $D\in\mathbb Q^\times$ is nonsquare over $\mathbb Q$ and square in $\mathbb Q_{13}$. The substitution $t\mapsto\sqrt{3/D}\,t$ identifies its local denominator with $1-3t^2$, preserving $t=0$. The local integrality and nonconstant-reduction arguments for cubic numerators apply to this normalized coordinate. Hensel's lemma lifts the chosen simple residue root to $\alpha\in\mathbb Q_{13}$. Vanishing of $X$ there means the original rational numerator vanishes at one root of $1-Dt^2$. That polynomial is irreducible over $\mathbb Q$, so it divides the numerator globally and $x=X/(1-Dt^2)^3$ has pole order at most two. The pole-order-two result then forces a constant family. [Integral reduction and global argument](CubicPellAt13.md) · [Pole order two](pole_two.md)

The local obstruction also works over $\mathbb F_{169}$ after unramified splitting of a nonsquare unit denominator at 13. The same proof permits any unit $e$ and any simple root with nonzero derivative. The nonsplit residue enumeration and the opposite orientation of $z$ are included in the global calculation. [Cubic Pell models at 13](CubicPellAt13.md)
