# Quartic Pell substitutions through (1,0,1) fixed by reflection

Let $u^2 - Dv^2 = 1$ for a nonsquare rational $D$, and consider a reflection-symmetric quartic substitution

$$
x = C(u), \qquad y = v E(u), \qquad z = J(u),
$$

where $C, E, J \in \mathbb{Q}[u]$ have $\deg C = 4$, $\deg E \le 2$, $\deg J \le 6$, and $C(1) = J(1) = 1$. The cubic surface equation becomes

$$
C^3 + J^2 + k(u^2 - 1) E^2 J = 2, \qquad k = \frac{1}{D}.
$$

**No such substitution takes an integer value at the second endpoint $u = -1$.** In particular, no substitution of this form can have integer coefficients. More generally, write $(-C(-1), J(-1)) = nP$ on the elliptic curve $Y^2 = X^3 + 2$, where $P = (-1, 1)$. The argument below proves $|n| > 100$. The facts that $P$ generates the Mordell-Weil group and that $(-1, \pm 1)$ are the only integral points come from [LMFDB curve 1728a1](https://www.lmfdb.org/EllipticCurve/Q/1728a1/).

## Reducing coefficients of arbitrary height

Set $t = u - 1$ and $H = k t(t + 2) E^2$. Then $C(0) = J(0) = 1$ and $J(J + H) = 2 - C^3$. For an odd prime $p$, let $h$ be the maximum of $-v_p(a_i)/i$ over all nonzero positive-degree coefficients of $C, J, H$. Pick $\lambda$ with $v_p(\lambda) = h$ in a totally ramified extension (a root of a uniformizer gives any rational valuation without changing the residue field). Then $C(\lambda T), J(\lambda T), H(\lambda T)$ have integral coefficients and at least one nonconstant term survives reduction.

The reduced polynomial $\bar H$ cannot be zero: otherwise $C^3 + J^2 = 2$ defines a smooth genus-1 curve, which has only constant rational-function points by the constant-fiber theorem in [PellConstantFiber.lean](PellConstantFiber.lean). Because the Gauss valuation of a square is twice that of its base, normalizing the reduction of $E(\lambda T)$ to be monic writes $\bar H = k' R e^2$ for some $k' \in \mathbb{F}_p^\times$ and monic $e$ with $\deg e \le 2$, where:

* $R = T$ if $h > 0$,
* $R = T^2$ if $h < 0$,
* $R = T(T + 2)$ if $h = 0$ (taking $\lambda = 1$).

For each of the $p^4$ candidate polynomials $C$ with $C(0) = 1$, [quartic_reflection.py](quartic_reflection.py) factors $2 - C^3$, checks every divisor $J$ where both $J$ and $(2 - C^3)/J$ have degree at most 6, scales $J$ to $J(0) = 1$, and tests whether $(2 - C^3)/J - J$ has the required form $k' R e^2$. The table counts nonconstant solutions with monic $e$:

| Prime | $R = T$ | $R = T^2$ | $R = T(T + 2)$ | Order of $P$ | Allowed indices $n$ modulo that order |
| --- | ---: | ---: | ---: | ---: | --- |
| 11 | 0 | 140 | 46 | 12 | 1, 3, 5, 7, 9, 11 |
| 13 | 12 | 0 | 30 | 19 | 0, 1, 4, 6, 7, 8, 9, 10, 11, 12, 18 |
| 19 | 72 | 72 | 16 | 13 | 0, 1, 12 |

In every positive-scale ($h > 0$) residue at 13 and 19, $C$ keeps full degree 4. Its quartic term strictly dominates the lower terms at the original $t = -2$, so the second endpoint reduces to the point at infinity. When $h < 0$, every nonconstant coefficient has positive valuation, so the endpoint reduces to $P$. The remaining allowed residues come from evaluating each unit-scale ($h = 0$) model at $T = -2$. Since all three primes are primes of good reduction, $nP$ reduces to $n\bar P$.

At both 13 and 19, the surviving positive indices of $C, J, H$ in every positive-scale residue also have gcd 1. For any surviving index $i$, the original rational coefficient has valuation $-ih \in \mathbb{Z}$, so $h$ must be an integer. Every nonintegral endpoint at 13 or 19 therefore has $v_p(C(-1)) = -4h$, a multiple of 4.

Exact group addition gives $v_{13}(X(19P)) = -2$ and $v_{19}(X(13P)) = -2$. In general, if $13 \mid n$ and $19 \nmid n$, then $(n/13)(13P)$ has the same $X$-valuation as $13P$ at 19 (in the formal parameter $-X/Y$ at infinity, multiplication by $m$ has leading term $mT$ with integral higher terms at a prime of good reduction, and $v(X) = -2v(T)$). Swapping 13 and 19 gives the converse, so any candidate index must satisfy $13 \mid n \iff 19 \mid n$.

Checking the rational multiples $nP$ directly for $1 < |n| \le 100$, the mod-11/13/19 constraints and the valuation-divisible-by-4 test leave only seven indices: $-77, -53, -51, -27, 25, 27, 77$. Four more prime checks eliminate them all:

| Prime | Excluded indices | Distinct endpoint values $(C(-1), J(-1))$ tested |
| --- | --- | --- |
| 47 | -77, -51, 77 | (6, 31), (6, 16) |
| 59 | -27, 25 | (28, 36), (43, 26) |
| 61 | -53 | (30, 5) |
| 97 | 27 | (46, 65) |

At each of these four primes, [quartic_reflection.py](quartic_reflection.py) verifies that no positive-scale model loses both maximal degrees, so $h > 0$ would force a nonintegral endpoint. Each listed point is finite and distinct from $(1, 1)$, ruling out $h < 0$ too. For $h = 0$, prescribing $C(-1)$ adds a linear constraint on $C$, leaving only $p^3$ choices, and none has a valid divisor $J$ giving the target endpoint.

## Equal integral endpoints

Suppose $C(-1) = J(-1) = 1$. At $p = 13$, the integral endpoint rules out $h > 0$, and there are no $h < 0$ residues. Only two unit-scale residues match $(1, 1)$ at $u = -1$. In the original variable $u$, both have even $C$ and $J$ and odd $e$. Fixing both endpoints gives 14 equations (12 coefficient equations plus 2 endpoint equations) in 13 variables (4 nonconstant coefficients of $C(t)$, 6 of $J(t)$, and 3 of $e(t)$), and the Jacobian has full column rank 13.

In any lift, we can normalize $E$ to have a 13-adic unit coefficient and absorb a unit square root via Hensel's lemma, fixing $k'$ to a chosen square-class representative in $\mathbb{Z}_{13}^\times$. The involution $(C(u), J(u), e(u)) \mapsto (C(-u), J(-u), -e(-u))$ fixes the residue, both exact endpoints, and the identity. Because the reduced Jacobian is injective, comparing digits inductively shows any two lifts in the same class coincide.

Hence $C$ and $J$ are even and $E = e_1 u$ over $\mathbb{Q}$. Putting $s = u^2$ makes $x$ and $z$ polynomials in $s$ of degrees at most 2 and 3, while $y^2 = (e_1^2/D) s(s - 1)$ with $e_1 \ne 0$ by the constant-fiber theorem. This defines a pointed conic with two nonsplit conjugate ends on which $x$ has pole order 2 and $(s, y) = (1, 0)$ gives the integral seed, contradicting the pole-order-2 theorem in [pole_two.md](pole_two.md).

## Opposite integral endpoints

Suppose $C(-1) = 1$ and $J(-1) = -1$. Again only $h = 0$ is possible at 13, leaving two residues, both with $(\deg \bar C, \deg \bar J, \deg \bar E) = (2, 3, 0)$ and nonzero constant $\bar E$. Normalize $k$ to a unit in $\mathbb{Q}_{13}$ as before and reverse the polynomials in $u$:

$$
A(s) = s^4 C(1/s), \quad B(s) = s^6 J(1/s), \quad F(s) = s^2 E(1/s).
$$

They satisfy $A^3 + B^2 + k(1 - s^2) F^2 B = 2 s^{12}$, and modulo 13 their vanishing orders at $s = 0$ are $(2, 3, 2)$. So $A'$ has a simple root at 0 modulo 13, which lifts by Hensel's lemma to a root $\alpha$ of $A'$. Expand $A, B, F$ in powers of $s - \alpha$ with coefficients $A_i, B_i, F_i$, and set (with $v(0) = +\infty$)

$$
r = \min\left\{\frac{v(A_0)}{2},\, \frac{v(B_0)}{3},\, \frac{v(B_1)}{2},\, v(B_2),\, \frac{2v(F_0)}{3},\, 2v(F_1),\, 2v(\alpha)\right\}.
$$

Every entry is positive, and $r$ is finite (otherwise $\alpha = 0$ and $s^2 \mid A$, contradicting $\deg C = 4$). Pick $\rho$ with $v(\rho) = r/2$ in a totally ramified extension and set $s = \alpha + \rho^2 T$. Then $A/\rho^4$, $B/\rho^6$, and $F/\rho^3$ are integral and reduce to polynomials $a, b, f$ of degrees $2$, $3$, and at most $1$, with no linear term in $a$. After dividing by $\rho^{12}$, the right-hand side reduces to $2c^6$ where $c = \overline{(\alpha/\rho)^2}$, and all higher terms vanish. By the choice of $r$, at least one of $a(0)$, the lower coefficients of $b$ (below degree 3), the coefficients of $f$, or $c$ is nonzero.

Put $w = 2b + \bar k f^2$, so

$$
w^2 = 8c^6 + \bar k^2 f^4 - 4a^3.
$$

Matching leading terms gives $w_3^2 = -4a_2^3$, so scaling $T$ normalizes the leading coefficients of $w$ and $a$ to $2$ and $-1$. The $T^5$ coefficient gives $w_2 = 0$, leaving the finite-field identity

$$
(2T^3 + dT + e)^2 = 8c^6 + \bar k^2 (mT + g)^4 - 4(-T^2 + a_0)^3.
$$

Lean proves in [QuarticReflection.lean](QuarticReflection.lean) that $a_0 = d = e = m = g = c = 0$, forcing $a$ and $b$ to be pure monomials and killing every term that could have attained the minimum $r$. This rules out the opposite endpoint. The normalization and specialization are written steps above; Lean checks the leading-coefficient scaling and the finite-field contradiction.

To reproduce the finite checks, run:

```sh
uv run --with python-flint==0.9.0 quartic_reflection.py
```
