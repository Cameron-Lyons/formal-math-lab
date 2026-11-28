# Polynomial graphs and linear Pell ordinates

Can we build a Pell family on $z^2 + y^2 z + x^3 = 2$ by taking $x = f(y)$ to be a high-degree polynomial in $y$, so that completing the square $(2z + y^2)^2 = y^4 + 8 - 4f(y)^3$ leaves a squarefree quadratic $q(y)$ after pulling out a polynomial square $e(y)^2$? And even more generally, could a Pell substitution on $u^2 - Dv^2 = 1$ have **$y$ of pole order $1$** at the two ends, with *no* restriction at all on the degree of $x$?

This document proves three unconditional bounds answering both questions in the negative and constraining all higher-degree Pell substitutions:

1. **Polynomial-graph bound:** If $f \in \mathbb{Q}[Y]$ satisfies $Y^4 + 8 - 4f(Y)^3 = q(Y)e(Y)^2$ with $\deg q \le 2$, and both $y_0$ and $f(y_0)$ are $7$-integral for some $y_0 \in \mathbb{Q}$, then **$\deg f \le 2$**.
2. **No linear Pell ordinate (any degree of $x$):** For any nonsquare $D \in \mathbb{Q}$, if a nonconstant polynomial substitution on $u^2 - Dv^2 = 1$ takes integer values in all three coordinates at some rational parameter, then **$y$ cannot have pole order $1$ at the two ends**, regardless of the degree of $x$.
3. **General pole-order ratio:** For any nonconstant Pell substitution where $x$ has pole order $n$ and $y$ has pole order $m$ at either conjugate end, **$n \le 8m$** (so, for example, pole order $2$ in $y$ caps $x$ at pole order at most $16$).

* **Verification split:** Lean verifies the characteristic-zero degree bound and both rescaled contradictions in [PolynomialGraph.lean](PolynomialGraph.lean), the constant-fiber theorem in [PellConstantFiber.lean](PellConstantFiber.lean), and the pole-order ratio $n \le 8m$ in [PellDegreeRatio.lean](PellDegreeRatio.lean). The exhaustive mod-$7$ search is in [polynomial_graph_mod7.py](polynomial_graph_mod7.py), and the $7$-adic Gauss-norm zooms and cubic-surface geometry are written out below.

## Step 1: A finite degree bound ($n \le 8$)

Set $H = Y^4 + 8$ and $n = \deg f$. Assume $n \ge 2$, so $4f^3$ dominates $H$ and $\deg(qe^2) = 3n$.

**The Wronskian trick:** Differentiate $H = 4f^3 + qe^2$ to get $H' = 12f^2 f' + q'e^2 + 2qee'$, then take $3Hf' - H'f$ to eliminate $f^3$ and $f^2$ cleanly:

$$
3Hf' - H'f = e(3qef' - q'ef - 2qfe').
$$

Because $e$ divides the left-hand side, its degree is bounded by $\deg(3Hf' - H'f)$ — provided that polynomial does not vanish! Its top term has degree $n + 3$ and leading coefficient $(3n - 4)\operatorname{lc}(f)$, which is nonzero for every integer $n \ge 2$. Therefore $\deg e \le n + 3$, and substituting into $3n = \deg(qe^2) \le 2 + 2\deg e$ gives

$$
3n \le 2 + 2(n + 3) \implies n \le 8.
$$

This bound is proved formally in [PolynomialGraph.lean](PolynomialGraph.lean).

## Step 2: 7-adic integrality and the six mod-7 reductions

Work with the $7$-adic absolute value on $\overline{\mathbb{Q}}_7$, normalized so $|7| < 1$. Recall that the **Gauss norm** $\|g\|$ of a polynomial is the maximum absolute value of its coefficients, and it is multiplicative: $\|gh\| = \|g\|\,\|h\|$.

### Why every coefficient of $f$ is 7-integral

Shift to $y_0$ and expand $f(y_0 + s) = \sum a_i s^i$. Suppose for contradiction that some $|a_i| > 1$ ($i > 0$). Choose $0 < |\lambda| < 1$ so that $\max_{i > 0} |a_i \lambda^i| = 1$ (every required radius is a rational power of $|7|$, so $\lambda$ exists in a finite extension). Then:

* $f(y_0 + \lambda t)$ has Gauss norm $1$ (integral coefficients) and reduces modulo the maximal ideal to a **nonconstant** polynomial $A(t)$.
* Since $Y^4 + 8$ has no root in $\mathbb{F}_7$ (testing $Y \in \{0, \pm 1, \pm 2, \pm 3\}$ gives $Y^4 + 8 \equiv 1, 2, 3, 5 \pmod 7$), $H(y_0 + \lambda t)$ reduces to a **nonzero constant** $h$.
* By multiplicativity of the Gauss norm, we can scale $q$ and $e$ to have Gauss norm $1$ (absorbing a unit into one factor) before reducing, so $h - 4A^3$ reduces to a square times a polynomial $q_0(t)$ of degree at most $2$.

Over an algebraic closure of $\mathbb{F}_7$, every component of $v^2 = q_0(t)$ dominating the $t$-line is a rational curve (genus $0$). Pulling back to that component gives a nonconstant rational point on $w^2 + 4a^3 = h$ over a rational function field, contradicting the characteristic-$7$ constant-fiber theorem in [PellConstantFiber.lean](PellConstantFiber.lean).

Hence all shifted coefficients $a_i$ are integral at $7$, and shifting back by the $7$-integral point $y_0$ shows **all coefficients of $f$ are integral at $7$**.

### Exhaustive mod-7 search up to degree 8

Now reduce $f$ modulo $7$ in the original variable $Y$. For every polynomial $\bar f \in \mathbb{F}_7[Y]$ of degree at most $8$, [polynomial_graph_mod7.py](polynomial_graph_mod7.py) strips out all even-multiplicity factors from $Y^4 + 8 - 4\bar f^3$ and checks whether the squarefree remainder has degree at most $2$.

* As a fast filter (which remains valid even for inseparable polynomials), it first checks $\deg\gcd(P, P')$ to verify that a large enough square factor can exist.
* Symmetry reductions: multiplying $\bar f$ by a cube root of unity reduces the leading coefficient to $1$ or $3$; at even degree, sending $Y \mapsto -Y$ normalizes the first nonzero odd coefficient; $\bar f = 0$ is checked separately.

Across all degrees up to $8$, **only six polynomials survive** modulo $7$:

$$
Y + 5, \qquad 3Y + 6, \qquad Y^2 + 2Y + 1, \qquad Y^2 + 2, \qquad Y^2 + Y + 4, \qquad 3Y^2 + 1.
$$

Crucially, **every one of the six leaves a squarefree factor of degree exactly $2$**. Scaling $q$ and $e$ to Gauss norm $1$ in any rational lift, the reduced polynomial $\bar q$ must account for both distinct roots. Therefore $\deg q = 2$, its leading coefficient is a $7$-adic unit, and both of its roots $\beta$ lie inside the unit disc: $|\beta| \le 1$.

## Step 3: Why the degree cannot increase in a 7-adic lift

We know $\deg \bar f \le 2$, and we now rule out any lift of strictly higher degree $n > \deg \bar f$ by zooming on $7$-adic discs of radius $> 1$ (where the tiny higher-degree terms of $f$ catch up with the $Y^4$ term of $H$). Let $\|g\|_R = \|g(\lambda T)\|$ denote the Gauss norm on a disc of radius $R = |\lambda|$.

### Case 1: $\bar f$ is quadratic and $n > 2$

Because $f$ has a nonunit leading coefficient (degree $> 2$) yet a unit $Y^2$ coefficient, $f$ must have at least one root $\gamma \in \overline{\mathbb{Q}}_7$ outside the unit disc, with $R = |\gamma| > 1$ (otherwise bounded roots and a nonunit leading coefficient would force every coefficient to be a nonunit).

Inspect $\|f(\gamma + \lambda T)\|$ as the disc radius $|\lambda|$ grows from $0$ to $R$:

* At $|\lambda| = 0$, $f(\gamma) = 0$.
* At $|\lambda| = R$, integral translation of $T$ preserves the Gauss norm, so $\|f(\gamma + \gamma T)\| = \|f(\gamma T)\| \ge R^2 > R^{4/3}$ (using the unit $Y^2$ coefficient).

Because the Gauss norm on discs varies continuously with radius, there exists $0 < |\lambda| < R$ where $\|f(\gamma + \lambda T)\| = R^{4/3}$. Divide $f(\gamma + \lambda T)$ by a cube root of $\gamma^4$ and reduce: this produces a **nonconstant** polynomial $A$ with $A(0) = 0$.

Meanwhile, on this disc $|\lambda| < R = |\gamma|$:

* $H(\gamma + \lambda T)/\gamma^4 = (1 + (\lambda/\gamma)T)^4 + 8/\gamma^4$ reduces to $1$;
* because both roots of $q$ satisfy $|\beta| \le 1 < R$, we have $|\gamma - \beta| = R > |\lambda|$, so $q(\gamma + \lambda T)/q(\gamma)$ also reduces to $1$.

Picking a square root of $q(\gamma)$ and dividing the identity $H - 4f^3 = qe^2$ by $\gamma^4$ keeps the normalized $e$ integral (by multiplicativity of the Gauss norm). Its reduction $B$ satisfies $B^2 + 4A^3 = 1$, forcing $A$ to be constant — contradicting nonconstancy of $A$.

### Case 2: $\bar f$ is linear and $n \ge 2$

Here we work on discs centered at $0$. Because only the constant and linear coefficients of $f$ can be units:

* for $R > 1$ very close to $1$, the linear/constant terms dominate and $\|f\|_R / R^{4/3} \le R / R^{4/3} < 1$;
* for sufficiently large $R$, the degree-$n$ term ($n \ge 2$) dominates and $\|f\|_R / R^{4/3} > 1$.

Pick $R = |\lambda| > 1$ where $\|f\|_R = R^{4/3}$, substitute $Y = \lambda T$, and divide the identity by $\lambda^4$:

* the normalized $f$ reduces to a **nonzero** polynomial $A(T)$;
* $H(\lambda T)/\lambda^4 = T^4 + 8/\lambda^4$ reduces to $T^4$;
* because both roots of $q$ satisfy $|\beta| \le 1 < R$, $q(\lambda T)/\lambda^2$ reduces to a nonzero scalar multiple of $T^2$.

Over an algebraic closure of $\mathbb{F}_7$, absorbing the scalar and $T^2$ into $B^2$ gives $B^2 + 4A^3 = T^4$. Now make the slick substitution $T = s^3$ and divide by $s^{12}$: the constant-fiber theorem forces $A(s^3)/s^4$ to be a constant! That is impossible, because $A(s^3)$ is a nonzero polynomial in $s^3$ (all exponents are multiples of $3$) and can never be a nonzero scalar multiple of $s^4$.

These two contradictions prove $\deg f \le 2$. The formal residue identities are checked in [PolynomialGraph.lean](PolynomialGraph.lean).

## Step 4: Why a linear Pell ordinate forces a polynomial graph

Now we show how the geometry of the cubic surface removes the polynomial-graph hypothesis altogether whenever $y$ has pole order $1$ on a nonsplit Pell conic!

**The big idea:** Slice the cubic surface $S$ by $y = Y$. The generic fiber is an elliptic curve $E/\mathbb{Q}(Y)$ with point at infinity $O$. By computing the Galois action on the $27$ lines of $S$, we prove $E(\mathbb{Q}(Y)) = \{O\}$ — the generic fiber has **no** other $\mathbb{Q}(Y)$-rational points! Now when $y$ has pole order $1$ on a Pell conic, the conic is a degree-$2$ cover of $\mathbb{P}^1_y$ with involution $\sigma$. The point $P = (x, 2z + y^2) \in E$ then has its trace $P + \sigma P$ defined over $\mathbb{Q}(y)$, forcing $P + \sigma P = O$, i.e., $\sigma P = -P$. Because elliptic inversion flips $2z + y^2$ while **fixing $x$**, $x$ must be $\sigma$-invariant — hence a polynomial $f(y)$!

Here are the exact geometric details:

1. **The rational Picard group of $S$ is $\mathbb{Z} H$:** Consider the smooth projective cubic surface $S : x^3 + y^2 z + z^2 w = 2w^3$. As proved in [QuarticGeometry.md](QuarticGeometry.md), its $27$ geometric lines split into **two Galois orbits** of sizes $3$ (the plane section $z = 0$) and $24$ (whose slopes are the roots of the irreducible polynomial $T^{24} + 540T^{12} - 108$). The geometric Picard group $\operatorname{Pic}(S_{\overline{\mathbb{Q}}})$ is torsion-free and generated by the $27$ lines; see [Huybrechts, *The Geometry of Cubic Hypersurfaces*, section 3.4](https://www.math.uni-bonn.de/people/huybrech/Notes.pdf). Their sum is $9H$ for the hyperplane class $H$ (summing the $45$ tritangent plane sections counts each line five times). Averaging over the Galois group shows that the rational Picard space is spanned by the two orbit sums $H$ and $8H$. Because $H$ meets a line with degree $1$, every Galois-invariant integral divisor class on $S$ is an integer multiple of $H$.
2. **Triviality of $E(\mathbb{Q}(Y))$:** Let $E/\mathbb{Q}(Y)$ be the generic fiber $(2z + Y^2)^2 = Y^4 + 8 - 4x^3$ with identity $O = [0 : 0 : 1 : 0]$. Any section distinct from $O$ would sweep out a $\mathbb{Q}$-rational curve $C \subset S$ of divisor class $rH$ for some $r \in \mathbb{Z}$. Away from $w = 0$, $C$ meets the smooth generic plane cubic in its defining point $P$ with multiplicity $1$, and $O$ is its only point at infinity, so its intersection divisor on $E$ is $P + (3r - 1)O$. Since the plane at infinity cuts out $3O$, the class $rH$ restricts on $E$ to $3rO$, making $P - O$ principal and forcing $P = O$. (The same divisor-class equality holds after extending constants to $\overline{\mathbb{Q}}$.)
3. **Descent to $x = f(y)$ and completion of the proof:** Now take a nonsplit Pell conic where $y$ has pole order $1$ at each of the two ends. Then $y$ has degree $2$ as a map to $\mathbb{P}^1$, so the function field of the conic is a quadratic extension of $\mathbb{Q}(y)$ with nontrivial involution $\sigma$. The point $P = (x, 2z + y^2)$ satisfies $P + \sigma P = O$ by the triviality of $E(\mathbb{Q}(Y))$. Since elliptic inversion negates $2z + y^2$ and fixes $x$, we obtain $x \in \mathbb{Q}(y)$. Because all poles of $x$ lie over the ends of the conic — which are precisely the poles of $y$ — $x = f(y)$ must be a **polynomial** in $y$.
4. **Reduction to pole order $\le 2$:** The $\sigma$-anti-invariant function $2z + y^2$ squares to $H - 4f^3$. It cannot vanish identically because $H = Y^4 + 8$ is squarefree. Since the quadratic extension is the function field of a genus-$0$ curve, the squarefree part of $H - 4f^3$ has at most two geometric branch points, giving $H - 4f^3 = q e^2$ with $\deg q \le 2$. The marked integer point supplies a $7$-integral $y_0$ with $f(y_0)$ also $7$-integral, so Steps 1–3 force $\deg f \le 2$. Then $x = f(y)$ has pole order at most $2$ at each end, and [pole_two.md](pole_two.md) forces the entire map to be constant.

## Step 5: A bound when both coordinates have larger pole order

Finally, even when $y$ has pole order $m \ge 2$, the pole order $n$ of $x$ cannot outrun $m$ arbitrarily:

> **Theorem ([PellDegreeRatio.lean](PellDegreeRatio.lean)).** For any nonconstant Pell substitution, let $n$ and $m$ be the pole orders of $x$ and $y$ at either conjugate end. Then **$n \le 8m$**.

**Proof:** First, $m > 0$, because constant $y$ gives a smooth elliptic fiber with only constant maps from a rational curve. If $3n \le 4m$, then $n \le \tfrac{4}{3}m \le 8m$ holds immediately.

Otherwise, assume $k = 3n - 4m > 0$. Set $w = 2z + y^2$; the identity $w^2 + 4x^3 = y^4 + 8$ forces $w$ to have pole order $3n/2$ at both ends. Over the quadratic splitting field, choose a Laurent coordinate $t$ with ends at $0$ and $\infty$, and clear denominators to form ordinary polynomials

$$
a = t^n x, \qquad b = t^m y, \qquad c = t^{3n/2} w,
$$

which have degrees $2n$, $2m$, $3n$ and nonzero constant terms. Setting $h = b^4 + 8t^{4m}$ (so $\deg h \le 8m$ and $h(0) = b(0)^4 \ne 0$), the surface equation becomes

$$
c^2 + 4a^3 = t^k h.
$$

Apply the logarithmic derivation $\delta = t\,d/dt$ to $c^2 + 4a^3 = t^k h$ to get $2c\,\delta c + 12a^2\,\delta a = t^k(kh + \delta h)$. Multiplying by $a$ and substituting $12a^3 = 3(t^k h - c^2)$ eliminates $a^3$ cleanly:

$$
c(3c\,\delta a - 2a\,\delta c) = t^k N, \qquad N = 3h\,\delta a - a(kh + \delta h).
$$

Hence $c \mid t^k N$. Because $c(0) \ne 0$, $c$ is coprime to $t^k$, so $c \mid N$. Moreover, the constant term of $N$ is

$$
N(0) = -k a(0) h(0) \ne 0,
$$

so $N$ is not identically zero! Comparing degrees immediately yields

$$
3n = \deg c \le \deg N \le \deg a + \deg h \le 2n + 8m \implies n \le 8m.
$$

In particular, when $y$ has pole order $2$, $x$ can have pole order at most $16$. This degree-ratio theorem is formally proved in [PellDegreeRatio.lean](PellDegreeRatio.lean).
