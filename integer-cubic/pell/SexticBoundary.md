# Ordinary sextic substitutions through an integer point

Suppose $x,y,z\in\mathbb Q[t]$ satisfy $z^2+y^2z+x^3=2$ and take integer values together at a rational parameter $t_0$. **If $\deg x\le6$ and $x(t_0)\not\equiv3\pmod5$, the family is constant.** In particular an ordinary polynomial family through $(0,1,1)$ needs degree at least seven in $x$. This result uses exact finite-field enumerations, a written valuation argument, and a Lean proof of the boundary obstruction. [Finite checker](SexticSearch.py) · [Lean boundary theorem](SexticBoundary.lean)

## Degree patterns

Degrees through five were excluded for every integer seed. Suppose $\deg x=6$. Each irreducible divisor of $z(z+y^2)=2-x^3$ has degree divisible by three because its residue field contains $\sqrt[3]2$. Constant factors would give a constant map by the genus-one argument. The two degrees therefore sum to 18 and are positive multiples of three. If unequal, the larger is even since their difference is $y^2$. Up to the involution $z\mapsto-z-y^2$, this leaves $(6,12)$ and $(9,9)$. In the first case $\deg y=6$ and the smaller choice of $z$ has degree six. Balancing at 13 gives a nonconstant solution over $\mathbb F_{13}$ with all three degrees at most six, already excluded. In the second case $\deg y\le4$. Write $W=2z+y^2$; then $W^2+4x^3=y^4+8$. [Smaller degrees](OrdinaryPolynomial.md) · [All-three-coordinates bound](CubicPellAt13.md#ordinary-polynomial-solutions-modulo-13)

## First scale at 5

Translate $t_0$ to zero. Let $h$ be the largest $-v_5(c_i)/i$ across all nonzero positive-degree coefficients of the three polynomials. In a totally ramified extension take $v(\lambda)=h$ and substitute $t=\lambda T$. All coefficients become integral and at least one nonconstant coefficient remains a unit. The residue field stays $\mathbb F_5$. If $\bar x$ were constant, both factors of $2-\bar x^3$ would be constant because $x(0)\not\equiv3\pmod5$. Then $\bar y$ would also be constant. Thus $\bar x$ is nonconstant.

There are 4075 orbits of nonconstant polynomials $\bar x$ of degree at most six under $T\mapsto cT+d$, $c\ne0$. For each representative, the checker factors $2-\bar x^3$, enumerates its divisors of degree at most nine including every scalar, then tests if $(2-\bar x^3)/\bar z-\bar z$ is a square of degree at most eight. It finds 12 pairs and each has degree profile $(4,3,6)$. Their leading coefficients in $\bar x$ always belong to $\{2,4\}$, independent of the change of variable because $c^4=1$ in $\mathbb F_5^\times$.

## Second scale at infinity

For the balanced polynomials, put $A(s)=s^6x(1/s)$, $B(s)=s^4y(1/s)$ and $E(s)=s^9W(1/s)$. They satisfy
$$
E^2+4 A^3 = s^2B^4+8s^{18}.
$$
Modulo the maximal ideal, $A$ starts at $s^2$ with coefficient $a\in\{2,4\}$, $B$ starts at $s$ with nonzero coefficient $b$, and $E$ is divisible by $s^3$. The constant coefficient of $A$ is nonzero in characteristic zero since $\deg x=6$. Use $v(0)=+\infty$ and take the minimum
$$
r=\min\{v(A_0)/2,\ v(A_1),\ v(B_0),\ v(E_0)/3,\ v(E_1)/2,\ v(E_2)\}>0.
$$
Take $v(\mu)=r$ in a further totally ramified extension. Substitute $s=\mu T$, dividing $A,B,E$ by $\mu^2,\mu,\mu^3$, respectively. The new coefficients are integral and some lower coefficient survives by the minimum. In the resulting residue identity the term $8s^{18}/\mu^6$ vanishes:
$$
e(T)^2=T^2(bT+w)^4-4(aT^2+vT+u)^3 .
$$
The Lean theorem implies $u=v=w=0$ for every $a\in\{2,4\}$ and $b\ne0$. It evaluates the right-hand side at the five elements of $\mathbb F_5$ and at $\sqrt2,2\sqrt2$ in the quadratic extension, where the norm of a square is a square. Independently, direct polynomial square-root tests reject all $2\cdot4\cdot(5^3-1)=992$ profiles with a surviving lower coefficient of $A$ or $B$. Once $A$ and $B$ reduce to their leading monomials, $e^2$ is a constant times $T^6$. Thus $e$ is zero or a multiple of $T^3$, contradicting the surviving lower coefficient.

## Remaining seeds

When $x(t_0)\equiv3\pmod5$, the first nonconstant reduction can have $\bar x=3$ and $\bar z=0$ or $-\bar y^2$. The previous argument handles every reduction with nonconstant $\bar x$; these two lines remain possible.

Independently, balancing at 13 forces the marked triple into a set of 116 out of the 130 surface points over $\mathbb F_{13}$. Indeed $\bar x$ is nonconstant by $2$ being a noncube, and all lower degrees are excluded. Depress the degree-six $\bar x$ by translation and take its leading coefficient as 1 or 2 by scaling the parameter and multiplying $\bar x$ by a cube root of unity. Both factors have degree nine, with equal leading coefficient since $\deg \bar y\le4$. Its square equals $-\bar x_6^3$, forcing $\bar x_6=1$. The checker factors over all $13^5$ remaining abscissas and finds 24 solutions counted by divisor and leading scalar. Evaluating at every field element, both signs of $\bar y$, and all cube-root twists gives the 116 points. This excludes $(1,0,1)$ at 13, but permits $(-2,3,1)$.

Run `uv run --with python-flint==0.9.0 SexticSearch.py --seeds-at-13` to reproduce both finite calculations.

## The seed $(-2,3,1)$

For this exceptional seed, translate each of the degree-six candidates at 13 to every parameter value giving the mark, and restore every allowed cube-root twist and sign. Every candidate has nonzero derivative of $x$ at this point. In a hypothesized rational map the balancing radius at 13 must therefore be integral, since the first coefficient of $x$ becomes a unit. A unique rational scaling makes $x'(0)=1$ and preserves integral coefficients at 13. After this normalization all modular candidates through this mark give the same triple.

Fix the constant terms exactly at $(-2,3,1)$ and fix $x_1=1$. The remaining 18 coefficients are $x_2,\ldots,x_6$, $y_1,\ldots,y_4$, $z_1,\ldots,z_9$. The equations are the 18 nonconstant coefficients of $x^3+zy^2+z^2-2$. Their Jacobian is invertible modulo 13, so each lift is unique. The checker lifts 699 times and verifies the residual modulo $M=13^{700}$.

For **each of the 18 coefficients**, if it is rational in lowest terms, the larger of its absolute numerator and positive denominator must exceed $10^{388}$. For the computed residue $r$, produce two independent integer pairs $(a_i,b_i)$ satisfying $a_i\equiv rb_i\pmod M$ with $(|a_i|+|b_i|)10^{388}<M$. A fraction $A/B$ of height at most $10^{388}$ with the same residue would make each $a_i B-b_i A$ divisible by $M$ and smaller than $M$ in absolute value. Vanishing of both determinants forces $(A,B)=(0,0)$, a contradiction. The checker verifies the congruences, determinant bounds and independence exactly. This height statement concerns the coordinate normalized by $x'(0)=1$.

Use `uv run --with python-flint==0.9.0 SexticSearch.py --exceptional-seed` for the marked lifts and height certificates.
