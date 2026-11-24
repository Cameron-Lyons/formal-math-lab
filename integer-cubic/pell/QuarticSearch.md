# Quartic Pell substitutions through (0,1,1)

On the conic $u^2-3v^2=1$, the search found 66 quartic numerator triples modulo 7 that retain both poles of $x$. They form 12 symmetry classes. Every class lifts modulo 343. The bounded rational searches below produced no polynomial identity.

## Domain of the enumeration

Use $L=1-3t^2$, $u=(1+3t^2)/L$, $v=2t/L$. When $x$ has pole order four, $z$ and $z+y^2$ have pole order six and $y$ has order at most three. The orders of the two factors are positive multiples of three with sum twelve. If their orders differ, the larger is the order of their difference $y^2$, which must be even. This leaves the pair $(6,6)$. A constant factor would force $x$ to be constant. [Lean pole-order theorem](PoleOne.lean)

Write $x=X/L^4$, $y=Y/L^3$, $z=Z/L^6$, with numerator degrees at most 8, 6, 12 and constants $0,1,1$. Their equation is
$$X^3+ZY^2+Z^2=2L^{12}.$$
The search assumes the coefficients are integral at 7 and $\gcd(\bar X,\bar L)=1$. For every such $X$ the polynomial $2L^{12}-X^3$ has degree 24 modulo 7, since 2 is not a cube in that field. Both $Z$ and $Z+Y^2$ have degree at most 12, so both must have degree 12. The program factors $2L^{12}-X^3$, enumerates the degree-12 divisors normalized by $Z(0)=1$, and tests whether the complementary factor minus $Z$ is a square. Its sign is fixed by $Y(0)=1$.

There are $7^8-7^6$ possible numerators $X$ before symmetry. The actions $t\mapsto-t$ and $X\mapsto\zeta X$ for $\zeta^3=1$ leave 941,535 orbits. The program tested 917,690 normalized divisors across them. The cube-root symmetries are defined modulo 7 and over $\mathbb Z_7$; rationality searches must account for all twists. [Complete search](search_quartic_pell.py) · [Twelve surviving triples and their orbit sizes](quartic_orbits_mod7.jsonl)

| Pole order of $y$ modulo 7 | Jacobian rank | Triple orbits | Triples before symmetry |
|---|---:|---:|---:|
| 2 | 24 | 1 | 6 |
| 3 | 20 | 9 | 48 |
| 3 | 24 | 2 | 12 |

## Lifts modulo 343

Fix the three constant terms. There are 26 correction digits and 24 coefficient equations. At rank 20 the first correction is an affine space with six free digits. The next correction is possible precisely when four quadratic expressions in those digits vanish, obtained by projecting the residual divided by 49 to the left kernel of the Jacobian. The checker derives these expressions from the polynomial identity and multiplies out a representative second lift for every surviving digit choice.

For each of the six pilot triples, exactly 98 of the 117,649 first lifts extend. Each of the 98 has 117,649 extensions, giving **69,177,612 triples modulo 343** across the pilot. For a representative, Lean proves that the four obstruction equations leave two digits arbitrary and a third in $\{1,-1\}$, determining the other three. The Python checker links the equations to the computed Jacobian. [Lean certificate](QuarticLift.lean) · [Lift checker](quartic_first_lifts.py)

For the entire search, the two rank-20 orbits of size three have 49 extendible first corrections per residue. Each of the seven rank-20 orbits of size six has 98. Each rank-24 residue has 49 first corrections, all with 49 extensions. This gives **518,875,308** triples modulo 343. For each surviving rank-20 correction, the four projected quadratics have Jacobian rank four in the six free digits. To see why this gives lifts to arbitrary precision, write the coefficient vector as a base lift plus $7K u+49v$, where the columns of $K$ lift a basis of the first Jacobian kernel. Every coefficient equation is divisible by 49 as a polynomial in $u,v$. After division, the derivative in $v$ spans the original rank-20 image, and the derivative in $u$ has rank four in its cokernel at each surviving digit choice. The combined derivative has full rank 24, so multivariate Hensel lifting applies. Thus every initial quartic residue class here admits a 7-adic lift.

## Rational models

The nine rank-20 orbits are obtained over $\mathbb F_7$ from the polynomial pattern
$$x=3s^4,\qquad y=1+3s^3,\qquad z=1-2s^3+2s^6,\qquad s=(ct+dt^2)/L.$$
Lean rules out even the larger rational family $x=bs+as^4$, $y=1+cs^3$, $z=1+fs^3+es^6$, except the constant seed. For $b\ne0$, scale to $b=1$. The four coefficient equations imply that $c$ is a root of
$$175616c^9-1153260c^8+1366848c^7+230592c^6-112896c^5+19548c^4+4704c^3+288c^2+1.$$
There is no projective root modulo 11. The $b=0$ case follows directly from the coefficient equations. This argument concerns the indicated shapes, while lifts with additional terms remain possible. [Lean proof](QuarticSparse.lean)

For the unique orbit with reduced $y$ of order two, an exact rational lift with $y$ also of order at most two can be excluded. In the restricted coefficient system write $Y=LE$. The reduced triple is the pullback of a pole-$(2,1,3)$ triple under the Pell doubling map $t\mapsto 2t/(1+3t^2)$. The restricted upstairs and downstairs Jacobians both have determinant 2 at the displayed representatives modulo 7. Hensel existence downstairs and uniqueness upstairs force any such lift to be a pullback. The downstairs coefficients can be recovered by triangular rational equations with nonzero diagonals $2^i$. A rational lift would therefore contradict the order-two result through an integral seed. A lift could still have order three in $y$ while reducing to order two. [Doubling and Jacobian checks](search_quartic_pell.py) · [Order-two exclusion](pole_two.md)

Two bounded searches allow general mixed terms.

* **Bounding $x$ alone.** Use either the eight nonconstant numerator coefficients, or the basis $(u-1)^i$ for $1\le i\le4$ and $v(u-1)^j$ for $0\le j\le3$. Represent the coefficient vector as $a/d$ in lowest common terms. Through height $\max(d,|a_1|,\ldots,|a_8|)\le8$, the two bases give 657,962 and 625,523 vectors after the modulo-7 test. None admits rational $Y,Z$ of any coefficient height. A second search extends the bound to 24 for $d$ prime to 35. It combines all admissible $X$ residues modulo 5 and 7 by the Chinese remainder theorem. This leaves 1,491,351 numerator-basis candidates and 1,520,489 Pell-basis candidates. After testing other primes, only 11 and 15 respectively require factorization over $\mathbb Q$. None of the 26 has an admissible divisor giving a square. For an odd prime at which $X$ is integral, this sieve is valid regardless of the denominators of $Y,Z$. The factors $Z,Z+Y^2$ have unit constant terms and integral product. By multiplicativity of the coefficient Gauss norm both are integral, and then so is $Y$. [Rational coefficient search](quartic_rational_search.py)
* **Fixing two coefficients of $Y$.** On each rank-24 class, removing the columns for $Y_1,Y_2$ leaves an invertible minor. For each coefficient, 91 rational values of height at most 24 have the required residue. The checker lifts each of the 24,843 pairs across the three representatives to precision $7^{64}$. No pair reconstructs every coefficient of $Y,Z$ with both numerator and denominator at most $10^{26}$ in absolute value. The test covers all 18 rank-24 residue triples because cube-root twists preserve $Y,Z$ and reflection preserves the height bounds. [Rational slice search](quartic_rational_slices.py)

## Reproduction

```sh
uv run --with python-flint==0.9.0 search_quartic_pell.py --output /tmp/quartic.jsonl
uv run --with python-flint==0.9.0 quartic_first_lifts.py --orbits /tmp/quartic.jsonl
uv run --with python-flint==0.9.0 quartic_rational_slices.py /tmp/quartic.jsonl
uv run --with python-flint==0.9.0 quartic_rational_search.py /tmp/quartic.jsonl
uv run --with python-flint==0.9.0 cubic_chart_obstructions.py --forms
lake -d .. build
```

The separate cubic calculation records the three initial obstruction forms for each of the seven normalized charts, the valuation tests, and the two remaining high-slope cases. [Cubic chart calculations](cubic_chart_obstructions.md)
