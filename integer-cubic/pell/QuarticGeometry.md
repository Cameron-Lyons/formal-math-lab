# Cubic-field factors and local obstructions for quartic Pell models

Consider a quartic model through $(0,1,1)$ on $u^2-3v^2=1$. With $L=1-3t^2$ it satisfies
$$
X^3+Z Y^2+Z^2=2L^{12},\qquad
\deg(X,Y,Z)\le(8,6,12),\qquad (X,Y,Z)(0)=(0,1,1).
$$
Assume $X$ is coprime to $L$ over $\mathbb Q$. The two smooth rank-24 quartic components with reduced $y$ of pole order three pass the line-intersection test modulo 7. Over other primes the tests below exclude entire residue classes without a height bound. The computations use polynomial factorization and exact finite-field linear algebra. [Reproducible checker](quartic_local_geometry.py)

## A factorization over the cubic field

Put $\alpha=\sqrt[3]{2}$ and $K=\mathbb Q(\alpha)$. Over a splitting field the three polynomials $\alpha_i L^4-X$ for $\alpha_i^3=2$ are pairwise coprime. A common root would force $L=X=0$. Their product is $Z(Z+Y^2)$. Both factors have degree 12, since their product has degree 24 and the leading coefficient of $X/L^4$ is rational.

Let $U_i=\gcd(Z,\alpha_i L^4-X)$, scaled to $U_i(0)=1$. Their product is $Z$ because the three larger factors are coprime. The Galois group permutes the $U_i$ transitively, so each has degree four. Put $V_i=(\alpha_i L^4-X)/U_i$. Each $V_i$ has degree four and constant coefficient $\alpha_i$. The member indexed by $\alpha$ gives
$$
UV=\alpha L^4-X,\qquad N_{K/\mathbb Q}(U)=Z,\qquad
N_{K/\mathbb Q}(V)-N_{K/\mathbb Q}(U)=Y^2 .
$$
Here the norm multiplies the three coefficientwise conjugates. Conversely, these equations yield the surface identity by multiplicativity of the norm. Writing $U=A+B\alpha+C\alpha^2$ gives $N(U)=A^3+2B^3+4C^3-6ABC$. This replaces a choice among degree-12 divisors by two degree-four polynomials over $K$.

## Intersections with the 27 lines

The projective cubic surface has equation $x^3+y^2z+z^2w=2w^3$. The three lines $z=0$, $x=\alpha_i w$ cut out the plane $z=0$. Every other line can be written in the affine chart $w=1$ as $x=ay+b$, $z=cy+d$. There is no line in the cuspidal plane section $w=0$. At constant $y$, the affine fiber has equation $(2z+y^2)^2=y^4+8-4x^3$, which is irreducible even over an algebraic closure. For $a\ne0$ the four coefficient equations for a line yield
$$
c=-a^3,\qquad b=a^4r,\qquad d=-a^6(3r+1),\qquad
3r^2+6r+2=0,\qquad a^{12}(-26r-11)=6 .
$$
The 24 slopes are the roots of $a^{24}+540a^{12}-108$. Exact factorization over $\mathbb Q$ verifies irreducibility, so the 24 lines are conjugate.

The rational quartic map into the projective cubic is represented by the degree-12 homogenizations of $(XL^2,YL^3,Z,L^6)$. These have no common zero. At roots of $L$, the condition $\gcd(X,L)=1$ and the cubic identity ensure $Z\ne0$. The pullback of any plane section therefore has degree 12 unless the curve lies in that plane. Each horizontal line has pullback degree four by the factorization above. All sloped lines have the same pullback degree $d$ by conjugacy. Every sloped line meets a horizontal line at its point with $z=0$. Their common plane cuts the cubic in these two lines and a third line, counted with multiplicity. The image cannot be contained in this union of lines, since a nonconstant rational map contained in one of them would also be contained in all its distinct Galois conjugates. The sum of the three pullback degrees is 12, giving $d=4$ whether the residual line is horizontal or sloped.

For $p=5$ assume the chart coefficients are $5$-integral. The horizontal lines form two residue orbits of sizes one and two. Their pullback degrees must both be at least four even if $X$ loses poles upon reduction. Indeed $U_i(0)=1$, and $Z=U_i(Z/U_i)$ has $5$-integral coefficients and constant one. Multiplicativity of the polynomial Gauss norm implies both normalized factors are integral. Applying the same argument to $\alpha_iL^4-X$ shows $V_i$ is integral. Homogenizing before reduction consequently gives a nonzero degree-four common binary factor of the reductions of $Z$ and $X-\alpha_iL^4$, including any factors at infinity.

The checker enumerates all 157 quartic residues at 5. Exactly 109 pass the horizontal-line test. Of the 150 full-pole residues, 104 pass. A further 24 of these 104 have inconsistent first-lift equations modulo 25, leaving 80. The same line test excludes both residues where $x$ has reduced pole order three, leaving five additional possibilities of orders zero, one and two. For a sloped residue line its intersection degree is computed from the homogeneous gcd of $X-aYL-bL^4$ and $Z-cYL^3-dL^6$. Testing all 27 lines gives the same 109 candidates. [Line and rank computations](quartic_local_geometry.py)

## The primes 2 and 3 in the rational chart

At 2, retaining the poles in this chart requires $\bar X(1)=1$ because $\bar L=(t+1)^2$. For each of the 128 possible numerators $X$, factor $X^3$ in $\mathbb F_2[t]$, take all degree-bounded factors $Z$ with $Z(0)=1$, and require $X^3/Z-Z$ to be a square of degree at most 12. This gives seven triples. Their correction matrices for lifting to modulus 4 have rank 18 for four triples and rank 20 for three. In every case the augmented rank is one greater. **No chart with 2-integral coefficients and $\bar X(1)=1$ can satisfy the identity.** Lean verifies the inconsistency by an explicit left-nullspace witness for each of the seven triples. An integral polynomial in $u,v$ loses both poles modulo 2 in this chart, because the three homogenized generators $L,1+3t^2,2t$ all vanish modulo 2 at $t=1$. [Lean certificate](QuarticBadTwo.lean)

At 3, $\bar L=1$. All 6,561 possible $X$ give 759 triples by the same divisor and square test. Exactly 21 have compatible correction equations modulo 9. Every one of the 21 has $\deg \bar X\le4$, $\deg\bar Y\le3$ and $\deg\bar Z\le6$. In particular these are necessary coefficient divisibility conditions on any 3-integral rational chart regardless of height. They also hold for rescalings $t\mapsto3^h t$, $h\ge0$, whose resulting coefficients are integral at 3: $2(1-3^{2h+1}t^2)^{12}$ is always $2$ modulo 9.

## Integral coefficients in the original Pell coordinates at 2

The Pell-coordinate ring gives an additional test when the coefficients in $u,v$ are 2-integral. Put $w=u-1-v$. The relation is
$$
w^2=2(v^2-v)-2(1+v)w .
$$
Each coordinate of degree at most $d$ can be represented uniquely as $P(v)+wQ(v)$ with $\deg P\le d$, $\deg Q<d$, using $d=4,3,6$. In characteristic two the base and $w$ coefficients of the identity are
$$
P_x^3+P_y^2P_z+P_z^2=0,\qquad P_x^2Q_x+P_y^2Q_z=0 .
$$
The first equation gives ten choices of the three $P$'s with the prescribed seed. The second gives 1,040 six-polynomial residues. Work modulo 4 in the full ring by multiplying $P+wQ$ using the stated relation. Its 24 nonconstant coefficient equations give inconsistent first corrections in 1,008 cases. All 32 survivors satisfy $P_x=0$, $P_y=P_z=1$, and $Q_z=0$ modulo 2. In particular every such quartic substitution takes the parity $(0,1,1)$ on every integral Pell point. This test allows the poles to coalesce in the rational chart at 2.

To repeat the finite checks, run:

```sh
uv run --with python-flint==0.9.0 quartic_local_geometry.py --all-lines
```
