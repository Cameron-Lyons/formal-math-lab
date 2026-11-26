# Quartic Pell substitutions through (0,1,1)

On $u^2 - 3v^2 = 1$, an exhaustive search modulo 7 finds 66 quartic numerator triples that keep both poles of $x$. They group into 12 symmetry orbits, and every orbit lifts to modulus 343 (and in fact to $\mathbb{Z}_7$). None of the bounded rational searches below produces a rational polynomial identity.

## Domain of the enumeration

Set $L = 1 - 3t^2$, $u = (1 + 3t^2)/L$, and $v = 2t/L$. When $x$ has pole order 4, [PoleOne.lean](PoleOne.lean) proves that $z$ and $z + y^2$ both have pole order 6 and $y$ has pole order at most 3: the orders of $z$ and $z + y^2$ are positive multiples of 3 summing to 12, and if they differed, the larger would equal the pole order of $y^2$, which is even. That leaves $(6, 6)$ (a constant factor would force $x$ constant).

Write $x = X/L^4$, $y = Y/L^3$, $z = Z/L^6$ with $\deg(X, Y, Z) \le (8, 6, 12)$ and constant terms $(0, 1, 1)$. They satisfy

$$
X^3 + ZY^2 + Z^2 = 2 L^{12}.
$$

Assume the coefficients are integral at 7 and $\gcd(\bar X, \bar L) = 1$ modulo 7. Since 2 is not a cube in $\mathbb{F}_7$, $2L^{12} - X^3$ always has degree 24 modulo 7, forcing both $Z$ and $Z + Y^2$ to have degree 12. [search_quartic_pell.py](search_quartic_pell.py) factors $2L^{12} - X^3$, tests every degree-12 divisor normalized to $Z(0) = 1$, and checks whether $(2L^{12} - X^3)/Z - Z$ is a square (fixing the sign of $Y$ by $Y(0) = 1$).

Before symmetry there are $7^8 - 7^6$ candidate numerators $X$. Reducing by $t \mapsto -t$ and $X \mapsto \zeta X$ ($\zeta^3 = 1$) leaves 941,535 orbits, across which the script tests 917,690 normalized divisors. (Since the cube-root twists live over $\mathbb{F}_7$ and $\mathbb{Z}_7$, rational searches must test all three twists.) The 12 surviving orbits are saved in [quartic_orbits_mod7.jsonl](quartic_orbits_mod7.jsonl):

| Pole order of $y$ modulo 7 | Jacobian rank | Triple orbits | Triples before symmetry |
| --- | ---: | ---: | ---: |
| 2 | 24 | 1 | 6 |
| 3 | 20 | 9 | 48 |
| 3 | 24 | 2 | 12 |

## Lifts modulo 343

With the three constant terms fixed, there are 26 correction digits and 24 coefficient equations. At Jacobian rank 20, the first-order solutions form a 6-dimensional affine space over $\mathbb{F}_7$. A first lift extends to modulus 343 if and only if four quadratic equations in those six free digits vanish (obtained by projecting the mod-49 residual, divided by 49, onto the left kernel of the Jacobian). [quartic_first_lifts.py](quartic_first_lifts.py) derives these four quadratics directly from the polynomial identity and verifies an explicit second lift by multiplication for every surviving choice.

Across the 6 pilot triples, 98 of the 117,649 first lifts extend, and each of those 98 has 117,649 second extensions, giving **69,177,612 triples modulo 343**. On one representative, [QuarticLift.lean](QuarticLift.lean) proves that the four obstruction equations leave two digits free and restrict a third to $\{1, -1\}$, which uniquely fixes the remaining three.

Across all 66 mod-7 residues:

* The 2 rank-20 orbits of size 3 have 49 extendible first lifts per residue.
* The 7 rank-20 orbits of size 6 have 98 extendible first lifts per residue.
* Each of the 18 rank-24 residues has 49 first lifts, and each of those has 49 extensions.

In total there are **518,875,308** triples modulo 343. At every surviving rank-20 first lift, the four projected quadratics have Jacobian rank 4 in the six free digits. Writing the coefficient vector as a base lift plus $7Ku + 49v$ (where the columns of $K$ lift a basis of the first Jacobian kernel), every equation is divisible by 49 as a polynomial in $(u, v)$. After dividing by 49, the derivative in $v$ spans the original rank-20 image and the derivative in $u$ has rank 4 in its cokernel, so the combined derivative has full rank 24. Multivariate Hensel lifting therefore applies, proving that every one of the 66 residue classes lifts to $\mathbb{Z}_7$.

## Rational models

Over $\mathbb{F}_7$, all 9 rank-20 orbits follow the sparse pattern

$$
x = 3s^4, \qquad y = 1 + 3s^3, \qquad z = 1 - 2s^3 + 2s^6, \qquad s = \frac{ct + dt^2}{L}.
$$

In [QuarticSparse.lean](QuarticSparse.lean), Lean rules out even the broader rational family $x = bs + as^4$, $y = 1 + cs^3$, $z = 1 + fs^3 + es^6$ (other than the constant seed). For $b \ne 0$, scaling to $b = 1$ forces $c$ to be a root of

$$
175616c^9 - 1153260c^8 + 1366848c^7 + 230592c^6 - 112896c^5 + 19548c^4 + 4704c^3 + 288c^2 + 1,
$$

which has no projective root modulo 11. The case $b = 0$ fails directly from the coefficient equations. (Lifts that leave this sparse shape remain possible.)

For the unique orbit where reduced $y$ has pole order 2, no rational lift can keep $y$ at pole order 2 or less. Writing $Y = LE$, the mod-7 triple is the pullback of a pole-$(2, 1, 3)$ triple along the Pell doubling map $t \mapsto 2t/(1 + 3t^2)$. As checked in [search_quartic_pell.py](search_quartic_pell.py), both the upstairs and downstairs restricted Jacobians have determinant 2 modulo 7 at the representatives. Hensel existence downstairs and uniqueness upstairs force any such lift to be a pullback, and the downstairs coefficients are recovered over $\mathbb{Q}$ via a triangular system with nonzero diagonals $2^i$. A rational lift with $y$ of pole order at most 2 would therefore violate the pole-order-2 exclusion in [pole_two.md](pole_two.md). (A lift whose $y$ has pole order 3 but reduces to order 2 modulo 7 is still open.)

Two bounded searches cover general mixed terms:

### Bounding $x$ alone

[quartic_rational_search.py](quartic_rational_search.py) represents the eight nonconstant coefficients of $x$ as $a/d$ in lowest common terms, using either the numerator basis of $X(t)$ or the Pell basis $(u - 1)^i$ ($1 \le i \le 4$) and $v(u - 1)^j$ ($0 \le j \le 3$). Up to height $\max(d, |a_1|, \ldots, |a_8|) \le 8$, the mod-7 filter leaves 657,962 numerator-basis vectors and 625,523 Pell-basis vectors, none of which admits rational $Y, Z$ of any height. Extending to height 24 for $d$ coprime to 35 via the Chinese remainder theorem on mod-5 and mod-7 residues leaves 1,491,351 numerator-basis candidates and 1,520,489 Pell-basis candidates. Further prime filters cut these down to 11 and 15 vectors for exact factorization over $\mathbb{Q}$, and none produces a square. At any odd prime where $X$ is integral, this sieve needs no denominator bound on $Y$ or $Z$: $Z$ and $Z + Y^2$ have unit constant terms and integral product, so multiplicativity of the Gauss norm forces $Z$, $Z + Y^2$, and $Y$ to be integral.

### Fixing two coefficients of $Y$

In each rank-24 class, dropping the $Y_1$ and $Y_2$ columns leaves an invertible minor. Each coefficient has 91 rational values of height at most 24 matching the mod-7 residue, giving 24,843 pairs across the three representatives. [quartic_rational_slices.py](quartic_rational_slices.py) lifts every pair to precision $7^{64}$ and finds no triple where all coefficients of $Y$ and $Z$ reconstruct with numerator and denominator at most $10^{26}$ in absolute value. Since cube-root twists fix $Y$ and $Z$ and reflection preserves height bounds, this covers all 18 rank-24 residue triples.

## Reproduction

```sh
uv run --with python-flint==0.9.0 search_quartic_pell.py --output /tmp/quartic.jsonl
uv run --with python-flint==0.9.0 quartic_first_lifts.py --orbits /tmp/quartic.jsonl
uv run --with python-flint==0.9.0 quartic_rational_slices.py /tmp/quartic.jsonl
uv run --with python-flint==0.9.0 quartic_rational_search.py /tmp/quartic.jsonl
uv run --with python-flint==0.9.0 cubic_chart_obstructions.py --forms
lake -d .. build
```

For the separate cubic chart calculation (initial obstruction forms on the seven normalized charts, valuation tests, and the two remaining high-slope cases), see [cubic_chart_obstructions.md](cubic_chart_obstructions.md).
