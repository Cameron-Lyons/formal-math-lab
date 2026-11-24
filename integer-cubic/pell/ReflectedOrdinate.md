# The plane projection of a quartic Pell substitution

Consider a chart on $u^2-3v^2=1$ through $(x,y,z)=(0,1,1)$ at $(1,0)$, with pole orders $4,\le3,\le6$ for $x,y,z$ at the two conjugate ends. Put $W=2z+y^2$, so $W^2=y^4+8-4x^3$. There is **no** rational reflection of the conic exchanging its two ends, fixing $x,y$, and negating $W$. The second marked value is unrestricted.

## Reduction over the quotient line

Over $\mathbb Q(\sqrt3)$, a reflection acts on the Laurent parameter $\xi=u+\sqrt3v$ by $\xi\mapsto c/\xi$. The sums of opposite Laurent powers are polynomials in an invariant linear coordinate, by the two-term recursion for $\xi^j+(c/\xi)^j$. Their differences are an anti-invariant linear coordinate times polynomials in the same invariant coordinate. The two rational eigenspaces on the linear polynomials descend over $\mathbb Q$. Write the invariant coordinate as $s=a(u-1)+bv$. When $b=0$, the reflection fixes the seed, contrary to $W(1,0)=3$. For $b\ne0$, an anti-invariant coordinate taking value one at the seed is $r=u+(3a/b)v$. In fact the two preimages of $s$ are obtained by changing the sign of $r$, since

$$r^2=1+(6a/b^2)s+(3/b^2)s^2.$$

Consequently the proposed chart would yield the one-variable identity

$$4X^3+QE^2=Y^4+8,\qquad Q=1+A s+3B^2s^2,\qquad B\ne0,$$

with $\deg X=4,\deg Y\le3,\deg E\le5$ and $(X,Y,E)(0)=(0,1,3)$. The factor $E$ occurs because $W=rE(s)$. Lean verifies the conic coordinate calculation. [Lean identities](ReflectedOrdinate.lean)

Normalize the valuation on $\mathbb Q_7$ by $v(7)=1$. For the nonzero positive-degree coefficients $c_i$ of $X$ and $Y$, take the maximum $h$ of $-v(c_i)/i$. In a totally ramified extension choose $\lambda$ of valuation $h$ and put $s=\lambda T$. Both rescaled polynomials become integral and at least one nonconstant coefficient survives. For the rescaled $Q,E$, the minima of their coefficient valuations are at most zero because their constant terms are units. The minimum for a product is the sum of the minima of its factors by multiplicativity of the Gauss norm. Since $QE^2=Y^4+8-4X^3$ is integral, both $Q$ and $E$ are therefore integral. Its quadratic coefficient $3(B\lambda)^2$ reduces either to zero or to three times a nonzero square.

Over $\mathbb F_7$, enumerate $X,Y$ by their four and three nonconstant coefficients. For each pair extract the factors of odd multiplicity in $Y^4+8-4X^3$. Their product, up to a scalar, must equal $Q$ unless $Q$ itself is a scalar times a linear square. In that case enumerate every linear factor of the square root. The constants $Q(0)=1$, $E(0)=3$ fix both scalar factors. In every surviving triple the coefficient of $T$ in $Q$ is nonzero. Thus $A\ne0$, $v(A)=-h$, and $h$ is an integer. Make the rational coordinate substitution $s=T/A$ so $Q_1=1$ exactly. Modulo 7 there are precisely the following six triples, with coefficients in ascending order. [Exhaustive checker](reflected_ordinate.py)

| $X$ | $Y$ | $E$ | $Q$ |
|---|---|---|---|
| $aT^2$, $a=1,2,4$ | $1+2T$ | $3+T+2T^2$ | $1+T-T^2$ |
| $3T+6T^2+5T^3$, $6T+5T^2+3T^3$, or $5T+3T^2+6T^3$ | $1+T+5T^2$ | $3+5T+T^2+T^3+2T^4$ | $1+T$ |

## The two possible degenerations at infinity

Write $a=S^4X(1/S),d=S^3Y(1/S),c=S^5E(1/S)$ and $q=S^2Q(1/S)$. Then

$$4a^3+qc^2=d^4+8S^{12}.$$

All four polynomials are integral over $\mathbb Z_7$. In both cases below take $v(0)=+\infty$. Coefficients indexed by $i$ refer to powers of $S-\alpha$.

**First row.** The reductions of $a,d,c$ have orders $2,2,3$ at zero, with leading coefficients $L\in\{1,2,4\},2,2$, and $q(0)\equiv-1$. By Hensel's lemma the derivative of $a$ has a root $\alpha$ in the maximal ideal, since its reduced linear coefficient is $2L\ne0$. Thus $a_1=0$. Set

$$\rho=\min\{v(a_0)/2,\ v(c_0)/3,\ v(c_1)/2,\ v(c_2),\
                2v(d_0)/3,\ 2v(d_1),\ 2v(\alpha)\}.$$

All entries are positive and the minimum is finite. Otherwise $\alpha=a_0=0$, contradicting $\deg X=4$. Choose $v(\mu)=\rho$ and a square root of $\mu$ in a totally ramified extension, for example by taking $\mu$ to be a suitable even power of a uniformizer. Substitute $S=\alpha+\mu T$ and divide $a,c,d$ by $\mu^2,\mu^3,\mu^{3/2}$, respectively. Every rescaled coefficient is integral. Higher terms drop in the residue equation, while $8S^{12}/\mu^6$ reduces to $8R^{12}$ with $R=\overline{\alpha/\sqrt\mu}$. The result is

$$4(LT^2+A_0)^3-(2T^3+C_2T^2+C_1T+C_0)^2=(lT+m)^4+8R^{12}.$$

The coefficient of $T^5$ forces $C_2=0$. Lean checks that the five coefficients from $T^4$ to $T^0$ then force $A_0,C_1,C_0,l,m,R$ all to vanish. This contradicts attainment of the minimum. [Quadratic boundary certificate](ReflectedOrdinate.lean)

**Second row.** The four polynomials $a,d,c,q$ each have a simple zero at zero after reduction. Choose $\alpha$ in the maximal ideal with $a(\alpha)=0$. Set

$$\rho=\min\{v(c_0),\ v(q_0),\ 4v(d_0)/3,\ 4v(\alpha)\}.$$

This number is positive and finite. An infinite value would give $\alpha=0$ and $q(0)=0$, contrary to the nonzero coefficient $3(B/A)^2$ of $T^2$ in $Q$. Choose $\mu$ of valuation $\rho$ with a fourth root in a totally ramified extension. Substitute $S=\alpha+\mu T$, dividing $a,c,q$ by $\mu$ and $d$ by $\mu^{3/4}$. Since $\bar q$ has linear coefficient one, the residue identity becomes

$$4(LT)^3+(T+Q_0)(vT+C_0)^2=D_0^4+8R^{12},\qquad v\ne0,$$

where $R=\overline{\alpha/\mu^{1/4}}$. The coefficients of $T^2,T,1$ force $C_0=Q_0=D_0=R=0$ over $\mathbb F_7$. This again contradicts the attained minimum. [Linear boundary certificate](ReflectedOrdinate.lean)

## Birational projection

Let $K=\mathbb Q(u,v)$ and $H=\mathbb Q(x,y,z)$. If the map to the normalization of the image has degree $k=[K:H]\ge2$, the normalization is rational by Lüroth's theorem. All poles are images of the two original ends. If both ends have one image, it is rational and the coordinates are ordinary polynomials with $\deg x=8/k\le4$, through the integral seed. This contradicts the earlier ordinary-polynomial exclusion. If the images are distinct, each has one geometric preimage and total ramification index $k$. They are conjugate quadratic points at infinity and the image has $x$-pole order $4/k\le2$, excluded by the order-one/two results. Hence $H=K$. [Ordinary-polynomial result](OrdinaryPolynomial.md) · [Order-one/two results](pole_two.md)

Since $W^2\in\mathbb Q(x,y)$, the projection to the $(x,y)$-plane now has degree one or two. In degree two its involution fixes $x,y$ and negates $W$. It permutes the two poles of $x$. Exchanging them has just been excluded. An involution fixing both ends acts by $\xi\mapsto-\xi$ on the split torus. Then $y$ has even pole order at most two, and the anti-invariant $W$ has odd pole order. But $W^2=y^4+8-4x^3$ has pole order twelve, so $W$ has order six. This proves $\mathbb Q(x,y)=\mathbb Q(u,v)$. The argument imposes no value at a second point.

## A fifteen-coefficient implicit equation

Give $x,y,W$ weights $4,3,6$. The irreducible plane equation $G(x,y)$ can be chosen monic of degree eight in $y$. Indeed the function $x$ defines a degree-eight map to $\mathbb P^1$ and $y$ is integral over $\mathbb Q[x]$: it has no poles above finite $x$. Since the projection is birational, the eight conjugates of $y$ over $\mathbb Q(x)$ are its eight branches above a generic $x$. At $x=\infty$ each branch grows with order at most $3/4$ relative to $x$, since each pole of $x$ has order four and each pole of $y$ has order at most three. Thus the coefficient of $y^j$ in $G$ has degree at most $\lfloor3(8-j)/4\rfloor$ in $x$. In particular the weighted degree of $G$ is exactly 24.

Let $C$ be the projective image and $H$ the hyperplane class on the smooth projective cubic surface. The computed intersections $C\cdot\ell=4$ for all 27 geometric lines imply $C\sim4H$: the lines generate the geometric Picard group, whose intersection form is nondegenerate. This uses the classical description as the blowup of the plane at six points. The divisor and its class are rational, and the one-dimensional section space cutting out this particular divisor descends to $\mathbb Q$. A section of $\mathcal O_S(4)$ is the restriction of a quartic in the ambient projective space, by the hypersurface exact sequence. Therefore in the affine coordinate ring of the surface, $C$ is defined, with multiplicity one, by a polynomial which reduces to $U(x,y)+V(x,y)W$. [Line intersection computation](QuarticGeometry.md) · [Picard group of a cubic surface](https://pmc.ncbi.nlm.nih.gov/articles/PMC7340950/)

The norm of the defining polynomial under $W\mapsto-W$ is a nonzero constant multiple of $G$. Its only zero divisor on the base is the projected curve, and the order is one because the projection is generically unramified there and $C$ maps birationally onto it. In particular $C$ differs from its conjugate: their coincidence would force $W=0$ identically, whereas $W=3$ at the seed. The identity reads
$$cG=U^2-(y^4+8-4x^3)V^2.$$
The weighted leading terms cannot cancel: $y^4-4x^3$ has odd degree in $x$ and is not a square in $\mathbb Q(x,y)$. Consequently $\deg_{\mathrm{wt}} U\le12$ and $\deg_{\mathrm{wt}} V\le6$. **Any candidate has a relation on just 15 monomials**: the eleven $x^iy^j$ with $4i+3j\le12$, and $W,Wy,Wy^2,Wx$. Its coefficient vector is unique up to a scalar. Indeed another relation with these bounds is a multiple in the affine coordinate ring; the norm of the multiplier has weighted degree zero, which by the same leading-term argument forces the multiplier to be constant.

For a chart with numerator triple $X,Y,Z$ and denominator $L=1-3t^2$, each column of the linear relation can be computed as the ordinary polynomial
$$X^iY^j(2Z+Y^2)^k L^{12-4i-3j-6k}.$$
Modulo 7 this matrix has rank 14 on two of the twelve known full-pole orbits and rank 10 on the other ten. All twelve pass this necessary condition. [Matrix check](reflected_ordinate.py)
