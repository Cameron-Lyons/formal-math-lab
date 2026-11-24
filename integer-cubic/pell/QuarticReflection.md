# Quartic Pell substitutions through (1,0,1) fixed by reflection

Let $u^2-Dv^2=1$, where $D$ is a nonsquare rational number. Consider
$$
x=C(u),\qquad y=vE(u),\qquad z=J(u),
$$
with rational polynomial coefficients, $\deg C=4$, $\deg E\le2$,
$\deg J\le6$, and $C(1)=J(1)=1$. The identity to be solved is
$$C^3+J^2+k(u^2-1)E^2J=2,\qquad k=1/D.$$

**No such substitution has an integral second endpoint at $u=-1$.**
In particular this excludes all integral-coefficient substitutions of this
form. More generally write $(-C(-1),J(-1))=nP$ on $Y^2=X^3+2$, where
$P=(-1,1)$. The argument below proves $|n|>100$. The use of the
Mordell–Weil generator and the list of integral points $(-1,\pm1)$ relies
on the elliptic-curve database. [Mordell–Weil group and integral points](https://www.lmfdb.org/EllipticCurve/Q/1728a1/)

## Reducing coefficients of arbitrary height

Write $t=u-1$ and $H=k t(t+2)E^2$. In this chart $C(0)=J(0)=1$, and
$J(J+H)=2-C^3$. For an odd prime $p$ take the greatest value of
$-v_p(a_i)/i$ over all nonzero positive-degree coefficients of $C,J,H$,
and call it $h$. Take a scalar $\lambda$ of valuation $h$ in a totally
ramified extension. Then $C(\lambda T),J(\lambda T),H(\lambda T)$ are
integral and some nonconstant coefficient survives. A root of a
uniformizer supplies any rational valuation needed here without changing
the residue field.

The reduced $H$ is nonzero: otherwise $C^3+J^2=2$ is a smooth
genus-one curve, hence has only constant rational-function points.
The constant-fiber theorem supplies the same conclusion in positive
characteristic. The Gauss valuation of a square is twice that of its
factor. After normalizing the reduction of $E(\lambda T)$ to be monic,
the reduced $H$ is $k' R e^2$ for $k'\in\mathbb F_p^\times$, $\deg e\le2$,
where $R=T$ if $h>0$, $R=T^2$ if $h<0$, and $R=T(T+2)$ if $h=0$ (take
$\lambda=1$). [Constant-fiber theorem](PellConstantFiber.lean)

For each of the $p^4$ possible abscissas with constant coefficient one,
the checker factors $2-C^3$ and finds every divisor $J$ of degree at most
six whose complementary divisor also has degree at most six. It scales
the divisor to have constant coefficient one, then tests whether
$(2-C^3)/J-J$ has the required square factorization. The table counts
nonconstant solutions with $e$ monic.

| Prime | $R=T$ | $R=T^2$ | $R=T(T+2)$ | Order of $P$ | Allowed indices $n$ modulo that order |
| --- | ---: | ---: | ---: | ---: | --- |
| 11 | 0 | 140 | 46 | 12 | 1, 3, 5, 7, 9, 11 |
| 13 | 12 | 0 | 30 | 19 | 0, 1, 4, 6, 7, 8, 9, 10, 11, 12, 18 |
| 19 | 72 | 72 | 16 | 13 | 0, 1, 12 |

In each positive-scale residue at 13 and 19, $C$ retains its maximal
degree four. In that case its quartic term strictly dominates every
lower term at the original $t=-2$, so the second endpoint reduces to
the point at infinity. For $h<0$, the original nonconstant
coefficients have positive valuation and the endpoint reduces to $P$.
The remaining column comes from evaluating each unit-scale model at
$T=-2$. All three curves have good reduction, so reduction of $nP$ is
the corresponding multiple of the reduced generator. At both 13 and 19, the greatest common divisor of the surviving positive
indices of $C,J,H$ in every positive-scale residue equals one. For any
surviving index $i$, the corresponding original rational coefficient has
valuation $-ih\in\mathbb Z$. Hence $h$ is an integer. Every nonintegral
endpoint therefore has $v_p(C(-1))=-4h$, a multiple of four.

For example, exact group addition gives $v_{13}(X(19P))=-2$ and
$v_{19}(X(13P))=-2$. More generally, if $13\mid n$ but $19\nmid n$,
the multiple $(n/13)(13P)$ has the same abscissa valuation as $13P$ at 19.
Indeed, in the formal parameter $-X/Y$ at infinity, multiplication by
$m$ has leading term $mT$ and integral higher coefficients at a prime
of good reduction, and $v(X)=-2v(T)$. Interchanging the two primes
gives the converse. Thus a prospective index satisfies
$13\mid n$ if and only if $19\mid n$.

For the finite bound the checker computes the rational multiples $nP$
directly and tests the two denominator valuations. Among all
$1<|n|\le100$, the three residue constraints and the divisibility-by-four
test leave precisely $-77,-53,-51,-27,25,27,77$. The following additional
tests eliminate them all.

| Prime | Excluded indices | Distinct endpoint values $(C(-1),J(-1))$ tested |
| --- | --- | --- |
| 47 | −77, −51, 77 | (6,31), (6,16) |
| 59 | −27, 25 | (28,36), (43,26) |
| 61 | −53 | (30,5) |
| 97 | 27 | (46,65) |

At each prime the program checks that no positive-scale model can lose
*both* maximal degrees, so $h>0$ would force a nonintegral endpoint.
The listed points are finite and distinct from the marked seed, also
excluding $h<0$. For $h=0$ the endpoint abscissa prescribes one more
linear coefficient constraint, leaving exactly $p^3$ possible $C$ to
test. None has an eligible $J$ at the required endpoint. [Complete finite checks](quartic_reflection.py)

## Equal integral endpoints

Suppose $C(-1)=J(-1)=1$. At 13 the integral endpoint and the preceding
degree result exclude $h>0$. There are no negative-scale residues.
Exactly two unit-scale residues have these endpoint values. In the
original variable $u$, both have $C,J$ even and $e$ odd. Their Jacobians
with both endpoints fixed have column rank 13 on 13 variables. The
checker uses the four nonconstant coefficients of $C(t)$, the six of
$J(t)$, and all three coefficients of $e(t)$. It appends the two
endpoint equations to the twelve coefficient equations.

For a lift we can fix $k'$ to a unit representing its square class
over $\mathbb Q_{13}$: normalize $E$ to have a unit coefficient and
absorb a unit square root by Hensel's lemma. The reflection
$(C(u),J(u),e(u))\mapsto(C(-u),J(-u),-e(-u))$ fixes the residue,
the exact endpoints and the identity. Injectivity of the reduced
Jacobian makes any two lifts in this residue class equal, by comparing
successive digits. Consequently $C,J$ are even and $E=e_1u$
over $\mathbb Q$. With $s=u^2$, both $x$ and $z$ are polynomials in
$s$ of degrees at most two and three, while
$y^2=(e_1^2/D)s(s-1)$. The coefficient $e_1$ is nonzero by the
constant-fiber theorem. The last equation is a pointed conic with
two conjugate nonsplit ends. On it $x$ has pole order two and the
point $s=1,y=0$ gives the integral seed. This contradicts the
order-two theorem. [Pole-order-two argument](pole_two.md)

## Opposite integral endpoints

Suppose $C(-1)=1$, $J(-1)=-1$. Again only the unit-scale chart is
possible at 13. There are two residues, both with
$(\deg \bar C,\deg\bar J,\deg\bar E)=(2,3,0)$, including a nonzero
constant $\bar E$. Work in the $u$-coordinate over $\mathbb Q_{13}$
with $k$ a unit after the same normalization. Reverse the polynomials:
$$
 A(s)=s^4 C(1/s),\quad B(s)=s^6 J(1/s),\quad F(s)=s^2E(1/s).
$$
They satisfy $A^3+B^2+k(1-s^2)F^2 B=2s^{12}$ and their reduced
orders of vanishing at zero are $(2,3,2)$. Thus $A'$ has a simple
root at zero modulo 13. Lift it to $\alpha$ with $A'(\alpha)=0$.
Write $A_i,B_i,F_i$ for the coefficients in powers of $s-\alpha$.
With $v(0)=+\infty$, set
$$
 r=\min\{v(A_0)/2,\ v(B_0)/3,\ v(B_1)/2,\ v(B_2),\
                 2v(F_0)/3,\ 2v(F_1),\ 2v(\alpha)\}.
$$
All entries are positive. If the minimum is infinite, $\alpha=0$
and $s^2$ divides $A$, already contradicting $\deg C=4$.
Otherwise take $v(\rho)=r/2$ and substitute $s=\alpha+\rho^2T$.
The integral polynomials $A/\rho^4,B/\rho^6,F/\rho^3$ reduce to
$a,b,f$ of degrees $2,3,\le1$, respectively, with no linear term in
$a$. The right-hand side after division by $\rho^{12}$ reduces to
$2c^6$ for $c=\overline{(\alpha/\rho)^2}$. All coefficients of higher
index disappear by their powers of $\rho$. The minimum defining $r$
ensures at least one of $a(0)$, the coefficients of $b$ below degree
three, the coefficients of $f$, or $c$ is nonzero.

Put $w=2b+\bar k f^2$. Then
$$w^2=8c^6+\bar k^2 f^4-4a^3.$$
The leading coefficients satisfy $w_3^2=-4a_2^3$, so scaling $T$
gives leading coefficients $2,-1$ for $w,a$. The degree-five
coefficient gives $w_2=0$. The remaining finite-field question
is now
$$
 (2T^3+dT+e)^2=8c^6+\bar k^2(mT+g)^4-4(-T^2+a_0)^3.
$$
Lean proves $a_0=d=e=m=g=c=0$. This forces $a,b$ to be pure
monomials and all designated lower coefficients to vanish, contrary
to the attained minimum. This excludes the opposite endpoint. The
normalization and specialization are written arguments; Lean verifies
the leading-coefficient scaling and finite obstruction.
[Kernel-checked local identity](QuarticReflection.lean)

Reproduce the finite checks with
`uv run --with python-flint==0.9.0 quartic_reflection.py`.
