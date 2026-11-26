# Polynomial graphs and linear Pell ordinates

Suppose $f \in \mathbb{Q}[Y]$ satisfies $Y^4 + 8 - 4f(Y)^3 = q(Y) e(Y)^2$ for polynomials $q, e \in \mathbb{Q}[Y]$ with $\deg q \le 2$. If both $y_0$ and $f(y_0)$ are integral at 7 for some $y_0 \in \mathbb{Q}$, then **$\deg f \le 2$**. In other words, a polynomial graph of degree 3 or higher through an integer solution cannot produce a Pell equation by pulling out a polynomial square.

Lean verifies the characteristic-zero degree bound and both contradictions after rescaling in [PolynomialGraph.lean](PolynomialGraph.lean). The finite-field search is in [polynomial_graph_mod7.py](polynomial_graph_mod7.py), and the passage to the residue field is given in writing below.

This result also constrains general polynomial substitutions on $u^2 - Dv^2 = 1$ for any nonsquare $D \in \mathbb{Q}$: if a nonconstant substitution takes integer values in all three coordinates at some rational parameter, then **$y$ cannot have pole order 1 at the two ends**, regardless of the degree of $x$. The fourth section below explains how the geometry of the cubic surface removes the polynomial-graph assumption in that case.

## A finite degree bound

Set $H = Y^4 + 8$ and $n = \deg f$. Assume $n \ge 2$, so $\deg(qe^2) = 3n$. Differentiating $H = 4f^3 + qe^2$ and eliminating $f^2$ gives

$$
3Hf' - H'f = e(3qef' - q'ef - 2qfe').
$$

The left-hand side has degree $n + 3$ and leading coefficient $(3n - 4)\operatorname{lc}(f) \ne 0$. Hence $\deg e \le n + 3$, and $3n \le 2 + 2(n + 3)$ forces $n \le 8$. This bound is proved in [PolynomialGraph.lean](PolynomialGraph.lean).

## Coefficient integrality and the six reductions

Use the 7-adic absolute value on $\overline{\mathbb{Q}}_7$ with $|7| < 1$. Shift to $y_0$ and expand $f(y_0 + s) = \sum a_i s^i$. Suppose some $|a_i| > 1$, and pick $0 < |\lambda| < 1$ so that $\max_{i > 0} |a_i \lambda^i| = 1$. (Every required radius is a rational power of $|7|$, so it exists in a finite extension.)

Then $f(y_0 + \lambda t)$ has integral coefficients and a nonconstant reduction $A(t)$. Since $Y^4 + 8$ has no root in $\mathbb{F}_7$, the polynomial $H(y_0 + \lambda t)$ reduces to a nonzero constant $h$. By multiplicativity of the Gauss norm, we can scale $q$ and $e$ to have Gauss norm 1 (absorbing a unit into one factor) before reducing, so $h - 4A^3$ reduces to a square times a polynomial $q_0(t)$ of degree at most 2. Over an algebraic closure, every component of $v^2 = q_0(t)$ dominating the $t$-line is rational. Pulling back to that component gives a nonconstant rational point on $w^2 + 4a^3 = h$ over a rational function field, which contradicts the characteristic-7 constant-fiber theorem in [PellConstantFiber.lean](PellConstantFiber.lean). Thus the shifted coefficients of $f$ are integral at 7, and shifting back by the 7-integral value $y_0$ shows all coefficients of $f$ are integral at 7.

Now reduce $f$ modulo 7 in the original variable $Y$. For every polynomial $\bar f$ of degree at most 8, [polynomial_graph_mod7.py](polynomial_graph_mod7.py) removes all even-multiplicity factors from $Y^4 + 8 - 4\bar f^3$. As a quick filter (which stays valid for inseparable polynomials), it first checks the degree of $\gcd(P, P')$ to ensure a large enough square factor can exist. Multiplying $\bar f$ by a cube root of unity reduces the leading coefficient to 1 or 3, and at even degree, sending $Y \mapsto -Y$ normalizes the first nonzero odd coefficient; $\bar f = 0$ is checked separately. Only six polynomials survive:

$$
Y + 5, \quad 3Y + 6, \quad Y^2 + 2Y + 1, \quad Y^2 + 2, \quad Y^2 + Y + 4, \quad 3Y^2 + 1.
$$

Every one of the six leaves a squarefree factor of degree exactly 2. Scaling $q$ and $e$ to Gauss norm 1 in any rational lift, the reduced $q$ must account for both distinct roots, so $\deg q = 2$, its leading coefficient is a 7-adic unit, and both of its roots satisfy $|\beta| \le 1$.

## The degree cannot increase in a lift

We rule out any lift of degree $n > \deg \bar f$ in both remaining cases.

When $\bar f$ is quadratic and $n > 2$, $f$ must have a root $\gamma$ with $R = |\gamma| > 1$ (otherwise the nonunit leading coefficient and bounded roots would force every coefficient to be a nonunit). Integral translation of $T$ preserves the Gauss norm, so $\|f(\gamma + \gamma T)\| = \|f(\gamma T)\| \ge R^2$, using the unit quadratic coefficient. At radius 0, $f(\gamma) = 0$. Because the Gauss norm on discs varies continuously with the radius, there is some $0 < |\lambda| < R$ where $\|f(\gamma + \lambda T)\| = R^{4/3}$. Dividing by a cube root of $\gamma^4$ and reducing gives a nonconstant polynomial $A$ with $A(0) = 0$.

On this disc, $H(\gamma + \lambda T)/\gamma^4$ reduces to 1, and since both roots of $q$ are bounded, $q(\gamma + \lambda T)/q(\gamma)$ also reduces to 1. Picking a square root of $q(\gamma)$ and dividing the identity by $\gamma^4$ leaves $e$ integral by multiplicativity of the Gauss norm. Its reduction $B$ satisfies $B^2 + 4A^3 = 1$, forcing $A$ to be constant, a contradiction.

When $\bar f$ is linear and $n \ge 2$, work on discs centered at 0. Since only the constant and linear coefficients of $f$ can be units, $\|f\|_R / R^{4/3} < 1$ for $R > 1$ close to 1, while the ratio exceeds 1 for large $R$. Pick $R = |\lambda| > 1$ where $\|f\|_R = R^{4/3}$, substitute $Y = \lambda T$, and divide the identity by $\lambda^4$. The normalized $f$ reduces to a nonzero polynomial $A$, and because both roots of $q$ are bounded, the normalized $q$ reduces to a nonzero scalar multiple of $T^2$. Over an algebraic closure, this gives $B^2 + 4A^3 = T^4$. Substituting $T = s^3$ and dividing by $s^{12}$, the constant-fiber theorem forces $A(s^3)/s^4$ to be constant. That is impossible, because $A(s^3)$ is a nonzero polynomial in $s^3$ and cannot be a nonzero scalar multiple of $s^4$.

These two contradictions prove $\deg f \le 2$. The formal residue identities are checked in [PolynomialGraph.lean](PolynomialGraph.lean).

## Why a linear Pell ordinate forces a polynomial graph

Consider the generic fiber at $y = Y$, which is the elliptic curve $E/\mathbb{Q}(Y)$ given by $(2z + Y^2)^2 = Y^4 + 8 - 4x^3$. We show its only $\mathbb{Q}(Y)$-rational point is the point at infinity $O$.

The smooth projective cubic surface $S$ is defined by $x^3 + y^2 z + z^2 w = 2w^3$. As shown in [QuarticGeometry.md](QuarticGeometry.md), its 27 geometric lines split into two Galois orbits of sizes 3 (the plane section $z = 0$) and 24 (whose slopes are the roots of the irreducible polynomial $T^{24} + 540T^{12} - 108$). The geometric Picard group is torsion-free and generated by the 27 lines; see [Huybrechts, *The Geometry of Cubic Hypersurfaces*, section 3.4](https://www.math.uni-bonn.de/people/huybrech/Notes.pdf). Their sum is $9H$ for the hyperplane class $H$ (summing the 45 tritangent plane sections counts each line five times). Averaging over the Galois group shows that the rational Picard space is spanned by the two orbit sums $H$ and $8H$. Because $H$ meets a line with degree 1, every Galois-invariant integral class is an integer multiple of $H$.

Any section distinct from $O$ would give a rational curve $C \subset S$ of class $rH$. Away from $w = 0$, $C$ meets the smooth generic plane cubic in its defining point $P$ with multiplicity 1, and $O = [0 : 0 : 1 : 0]$ is its only point at infinity, so its intersection divisor on the fiber is $P + (3r - 1)O$. Since the line at infinity cuts out $3O$, this divisor is equivalent to $3rO$, making $P - O$ principal and forcing $P = O$. (The same divisor-class equality holds after extending constants to $\overline{\mathbb{Q}}$.)

Now take a nonsplit Pell conic where $y$ has pole order 1 at each end. Then $y$ has degree 2 as a map to $\mathbb{P}^1$, so the function field of the conic is a quadratic extension of $\mathbb{Q}(y)$ with nontrivial automorphism $\sigma$. The point $P = (x, 2z + y^2)$ on the generic fiber satisfies $P + \sigma P = O$ by the result above. Since elliptic inversion negates $2z + y^2$ and fixes $x$, we get $x \in \mathbb{Q}(y)$. Because all poles of $x$ lie over $y = \infty$, $x = f(y)$ is a polynomial.

The anti-invariant function $2z + y^2$ squares to $H - 4f^3$. It cannot vanish identically because $H = Y^4 + 8$ is squarefree. Since the quadratic extension is the function field of a genus-0 curve, the squarefree part of $H - 4f^3$ has at most two geometric branch points, giving $H - 4f^3 = q e^2$ with $\deg q \le 2$. The marked integer point gives the 7-integral $y_0$, so the graph bound gives $\deg f \le 2$. Then $x$ has pole order at most 2 at each end, and [pole_two.md](pole_two.md) forces the map to be constant.

## A bound when both coordinates have larger pole order

For any nonconstant Pell substitution, let $n$ and $m$ be the pole orders of $x$ and $y$ at either conjugate end. Then **$n \le 8m$**.

Here $m > 0$, because constant $y$ gives a smooth elliptic fiber with only constant maps from a rational curve. If $3n \le 4m$, the bound holds immediately. Otherwise, put $w = 2z + y^2$; the equation $w^2 + 4x^3 = y^4 + 8$ forces $w$ to have pole order $3n/2$ at both ends. Over the quadratic splitting field, choose a Laurent coordinate $t$ with ends at $0$ and $\infty$, and set $a = t^n x$, $b = t^m y$, $c = t^{3n/2} w$. These are ordinary polynomials of degrees $2n, 2m, 3n$ with nonzero constant terms. Putting $k = 3n - 4m > 0$ and $h = b^4 + 8t^{4m}$, they satisfy

$$
c^2 + 4a^3 = t^k h.
$$

Apply $\delta = t\,d/dt$ to obtain $c \mid t^k N$, where $N = 3h\,\delta a - a(kh + \delta h)$. Since $c$ is coprime to $t$, $c$ divides $N$. The constant term of $N$ is $-k a(0) h(0) \ne 0$, so $N \ne 0$ and $3n = \deg c \le \deg N \le 2n + 8m$, giving $n \le 8m$. In particular, when $y$ has pole order 2, $x$ can have pole order at most 16. This degree-ratio theorem is proved in [PellDegreeRatio.lean](PellDegreeRatio.lean).
