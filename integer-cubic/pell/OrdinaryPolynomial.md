# Ordinary polynomial parametrizations through an integral point

Let $x,y,z\in\mathbb Q[t]$ satisfy $z^2+y^2z+x^3=2$ identically. Suppose $\deg x\le5$ and all three polynomials take integer values at some $t_0\in\mathbb Q$. **Then all three are constant.** The same proof only needs the three values to be integral at 13. The result concerns ordinary polynomials in one parameter. The finite-field calculations are reproducible in [ordinary_polynomial_search.py](ordinary_polynomial_search.py).

## Reduction to a nonconstant map over the residue field

Translate $t_0$ to zero. If any polynomial is nonconstant, take the maximum $h$ of $-v_{13}(a_i)/i$ over all its nonzero coefficients in positive degree and those of the other two polynomials. For $h=r/s$ in lowest terms, adjoin a root $\pi$ of $\pi^s=13$ to $\mathbb Q_{13}$. The extension is totally ramified by Eisenstein's criterion and has residue field $\mathbb F_{13}$. Substituting $t=\pi^r u$ makes every coefficient integral. At least one nonconstant coefficient is a unit, including when the maximum slope is zero or negative. The reduced triple therefore still solves the equation and at least one of its coordinates is nonconstant. Its first coordinate has degree at most five.

## Possible degrees

Work now in $\mathbb F_{13}[t]$, and put $z'=z+y^2$. The identity is $zz'=2-x^3$. Since 2 is a noncube in $\mathbb F_{13}$, a constant $x$ makes the product a nonzero constant, forcing $z,z',y$ to be constant. For a nonconstant $x$, neither factor vanishes identically.

Every irreducible factor of $z$ or $z'$ has degree divisible by three. Its residue field contains a root of the irreducible cubic $X^3-2$. Both $z$ and $z'$ must be nonconstant. Indeed, a constant $z_0\ne0$ gives $z_0 y^2=2-z_0^2-x^3$, a smooth genus-one curve since 2 is also a nonsquare modulo 13. A nonconstant map from the affine line would give a rational function field containing the function field of that curve, contrary to Lüroth's theorem. For constant $z'$ the solution $(x,y,-z')$ has constant third coordinate.

Write $d=\deg x$. The degrees of $z,z'$ are positive multiples of three summing to $3d$. If unequal, the larger degree equals $2\deg y$ and is even. The possibilities up to interchange are therefore

| $d$ | Degrees of $z,z'$ | Bound on $\deg y$ |
|---|---|---|
| 1 | none | |
| 2 | 3, 3 | $\le1$ |
| 3 | 3, 6 | $3$ |
| 4 | 6, 6 | $\le3$ |
| 5 | 3, 12 | $6$ |

## Two independent quartic checks

For $1\le d\le4$, translate the parameter so the coefficient of $t^{d-1}$ in $x$ vanishes. This is possible since $13\nmid d$. Under $t\mapsto at$ and $x\mapsto\zeta x$ the leading coefficient varies by $a^d\zeta$, where $a\ne0$ and $\zeta^3=1$. Keeping one leading coefficient in each coset and every lower coefficient gives respectively 1, 26, 169 and 8,788 candidates. The normalizations need only cover all equivalence classes; some representatives can be equivalent.

1. Factor $2-x^3$ and generate every monic divisor for which the divisor and quotient have degree at most six. For each of its 12 nonzero scalar multiples $z$, test if $(2-x^3)/z-z$ is a square. This tested 9,776 monic divisors and 117,312 multiples with zero hits.
2. Pair every normalized $x$ with every $y$ of degree at most three. Point evaluations at all 13 field elements leave 11,156 of the 256,592,024 pairs for which $y^4+8-4x^3$ could be a square polynomial. Squarefree factorization, including a check on the leading scalar, confirms that none are squares. This check does not factor $2-x^3$ or enumerate candidate $z$.

## Quintic check

For $d=5$, scaling and translation make $x$ monic with zero quartic coefficient, since fifth powers exhaust $\mathbb F_{13}^\times$. Thus there are $13^4$ lower-coefficient choices. Replacing $z$ by $-z-y^2$ preserves the equation, so we may take $\deg z=3$. Such a divisor of $2-x^3$ must be an irreducible cubic times a scalar. The checker tries every cubic factor and every nonzero scalar. None yields a square for $y^2$.

Degree six already admits residue examples. In increasing coefficient order one is $x=(5,5,2,5,2,0,1)$, $y=(1,4,5,0,10)$, $z=(8,4,3,7,1,2,7,5,2,5)$. Direct multiplication verifies the identity modulo 13.

## Osculating quadratic curves

A point $v^2=c^4+8$ also gives an explicit rational polynomial family. The quadratic with second-order contact at $(c,v)$ is
$$
 W(y)=v+\frac{2c^3}{v}(y-c)
       +\left(\frac{3c^2}{v}-\frac{2c^6}{v^3}\right)(y-c)^2 .
$$
Put $A=3c^8+48c^4-64$, $B=c^8-48c^4-192$. The contact identity reads
$$
 v^6\bigl(y^4+8-W(y)^2\bigr)=-8(y-c)^3(Ay+cB).
$$
For $y=(-v^6t^3/2-cB)/A$, $x=t(y-c)$ and $z=(W(y)-y^2)/2$, this gives $z^2+y^2z+x^3=2$. The coefficient $A$ is nonzero over $\mathbb Q$. Every member of this family misses even an integer value of $y$ at every rational parameter. Lean checks the polynomial identity and this sharper modulo-13 obstruction directly. [Osculating.lean](Osculating.lean)

Run the finite checks with

```sh
uv run --with python-flint==0.9.0 ordinary_polynomial_search.py
```
