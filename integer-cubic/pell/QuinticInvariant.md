# Quintic substitutions with a quadratic in the pole-one coordinate

Let $r$ be a function with simple poles at the two ends of a Pell conic, let $R$ be its value at the marked point, and set

$$a=2-R^3,\qquad z=(2-r^3)/a,\qquad x=r+qz.$$

**For $R\in\{0,1,-1,2,-2\}$ there is no such quintic substitution through $(0,1,1)$ with $q$ a quadratic polynomial in $r$.** The quadratic coefficients are unrestricted. The obstruction even holds over an algebraically closed field of characteristic zero. The exact discriminants and their squarefree decompositions can be reproduced with [the elimination script](quintic_invariant_elimination.py).

At the marked point $z=1$, so $q(R)=-R$. Write $q=-R+b(r-R)+c(r-R)^2$, with $c\ne0$ for a quintic. Set $h=2-r^3$. The original cubic equation requires

$$F(r)=a^2y^2=a^3-ah-3a^2r^2q-3arq^2h-q^3h^2.$$

The function $r$ defines a degree-two map from the smooth projective conic to the projective line. It has only two geometric ramification points, by Riemann–Hurwitz. Each root of odd multiplicity of $F$ must be a branch value, since its pullback is a square. The degree of $F$ is twelve with leading coefficient $-c^3$. Its squarefree part of odd multiplicities has degree at most two, so $\deg\gcd(F,F')\ge5$. Indeed an odd-multiplicity root uses at least one degree, an even-multiplicity root uses at least two, and there can be at most seven distinct roots in total.

In a one-parameter family of polynomials of fixed degree, the order of the discriminant at a parameter value is at least the degree of the gcd of the specialized polynomial with its derivative, when the leading coefficient is a unit there. The Sylvester determinant computes the resultant, its specialized corank is this gcd degree, and a determinant with corank $d$ vanishes to order at least $d$. The passage from the resultant to the discriminant divides by a unit.

Apply this observation first with parameter $c$ at fixed $b$. At a hypothetical solution the discriminant $\operatorname{disc}_r(F)$ vanishes to order at least five in $c$. The script divides it by a nonzero integer and $c^{18}$ to obtain $D(b,c)$, preserving multiplicities at $c\ne0$. For $R=0$, $D$ is a polynomial in $C=c^3$, and the substitution $c\mapsto c^3$ also preserves multiplicities at $c\ne0$. Use $v=C$ in this case and $v=c$ in the other four.

The leading coefficient of $D$ in $v$ is a nonzero integer independent of $b$ in each of the five computations. In particular its degree stays fixed at every candidate $b$. A root of multiplicity at least five in $v$ forces $\deg\gcd(D,D_v)\ge4$. Applying the determinant argument a second time shows that $b$ has multiplicity at least four in $\operatorname{disc}_v(D)$.

| $R$ | Degree in $b$ of the second discriminant | Squarefree blocks as (degree, multiplicity) |
|---|---:|---|
| $0$ | 252 | $(1,9),(15,3),(99,2)$ |
| $1,-1,2,-2$ | 816 | $(1,18),(48,3),(327,2)$ |

In each row the degree-one block is $b$ itself. Hence $b=0$. The exact specialization $D(0,v)$ is squarefree after removing its power of $v$, so no $v\ne0$ has multiplicity at least five. This excludes the proposed quintic.

```sh
uv run --with python-flint==0.9.0 python quintic_invariant_elimination.py
```
