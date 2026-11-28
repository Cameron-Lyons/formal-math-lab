# Quartic Pell substitutions through $(0, 1, 1)$

A natural strategy for producing infinitely many integer solutions to $z^2 + y^2 z + x^3 = 2$ is to map the Pell conic $u^2 - 3v^2 = 1$ (which carries infinitely many integer points) into the cubic surface via rational functions that pass through the integer seed $(0, 1, 1)$. Because lower-degree Pell substitutions are already ruled out, the first open case is a **quartic** substitution, where $x$ has pole order $4$ at the two points at infinity of the conic.

An exhaustive census modulo $7$ finds **66** quartic numerator triples that keep both poles of $x$. They fall into **12** symmetry orbits, and every orbit lifts to modulus $343$—and in fact all the way to the $7$-adic integers $\mathbb{Z}_7$—so $7$-adic local arithmetic alone does not rule out this family. Nevertheless, Lean excludes the sparse rational pattern appearing in the rank-$20$ orbits, a pullback argument rules out any rational lift whose $y$-coordinate keeps pole order at most $2$, and two large bounded searches find no rational polynomial identity.

## Setup and mod-7 enumeration

### Rational parametrization and pole orders

Parametrize the Pell conic $u^2 - 3v^2 = 1$ by the rational chart
$$
L = 1 - 3t^2, \qquad u = \frac{1 + 3t^2}{L}, \qquad v = \frac{2t}{L},
$$
which sends $t = 0$ to the base point $(u, v) = (1, 0)$ and puts the two conjugate "ends" at infinity at the roots of $L = 0$ ($t = \pm 1/\sqrt{3}$). The **pole order** of a function at these ends is simply the power of $L$ in its denominator.

When $x$ has pole order $4$, [PoleOne.lean](PoleOne.lean) proves that $z$ and $z + y^2$ must both have pole order $6$, while $y$ has pole order at most $3$:

* From $z(z + y^2) = 2 - x^3$, the pole orders of $z$ and $z + y^2$ are positive multiples of $3$ summing to $12$ (a constant factor would force $x$ constant).
* If those two pole orders differed, the larger would have to equal the pole order of $y^2$, which is even. The only pair of positive multiples of $3$ summing to $12$ that satisfies this constraint is $(6, 6)$.

Accordingly, write
$$
x = \frac{X}{L^4}, \qquad y = \frac{Y}{L^3}, \qquad z = \frac{Z}{L^6},
$$
where $X, Y, Z \in \mathbb{Q}[t]$ satisfy $\deg(X, Y, Z) \le (8, 6, 12)$ and constant terms $(X(0), Y(0), Z(0)) = (0, 1, 1)$. Clearing denominators turns the cubic surface equation into
$$
X^3 + ZY^2 + Z^2 = 2L^{12}.
$$

### Exhaustive search modulo 7

Assume the coefficients of $X, Y, Z$ are integral at $7$ and that $x$ keeps its poles modulo $7$, meaning $\gcd(\bar X, \bar L) = 1$ in $\mathbb{F}_7[t]$.

1. **Forced degree of factors.** Because $2$ is not a cube in $\mathbb{F}_7$, the leading terms of $2L^{12}$ and $X^3$ cannot cancel, so $2L^{12} - X^3$ always has full degree $24$ modulo $7$. Since $\deg Z \le 12$ and $\deg(Z + Y^2) \le 12$, both factors must have exact degree $12$.
2. **Factorization test.** For each candidate $X$, [search_quartic_pell.py](search_quartic_pell.py) factors $2L^{12} - X^3$ over $\mathbb{F}_7[t]$, tests every degree-$12$ divisor $Z$ normalized by $Z(0) = 1$, and checks whether $(2L^{12} - X^3)/Z - Z$ is a square $Y^2$ (fixing the sign of $Y$ by $Y(0) = 1$).
3. **Symmetry reduction.** Before symmetry there are $7^8 - 7^6$ candidate numerators $X$ (all degree-$\le 8$ polynomials with $X(0) = 0$ that are not divisible by $L$ modulo $7$). Quotienting by the sign flip $t \mapsto -t$ and the cube-root twist $X \mapsto \zeta X$ ($\zeta^3 = 1$) leaves **941,535** orbits, across which the script tests **917,690** normalized divisors. *(Note: because the cube roots of unity $\zeta$ exist in $\mathbb{F}_7$ and $\mathbb{Z}_7$ but not in $\mathbb{Q}$, subsequent rational searches must test all three twists.)*

The **12** surviving orbits (66 triples in total) are stored in [quartic_orbits_mod7.jsonl](quartic_orbits_mod7.jsonl):

| Pole order of $y$ modulo $7$ | Jacobian rank | Triple orbits | Triples before symmetry |
| --- | ---: | ---: | ---: |
| 2 | 24 | 1 | 6 |
| 3 | 20 | 9 | 48 |
| 3 | 24 | 2 | 12 |

## Lifting to modulus 343 and to $\mathbb{Z}_7$

With the three constant terms fixed, there are **26** unknown nonconstant coefficients in $(X, Y, Z)$ and **24** nonconstant coefficient equations from $X^3 + ZY^2 + Z^2 = 2L^{12}$.

### Why rank-20 residues face quadratic obstructions

At a **rank-24** residue, the Jacobian has full row rank, so standard Hensel lifting applies immediately: each residue has $7^{26-24} = 49$ first-order lifts modulo $49$, and each extends in $49$ ways at every subsequent power of $7$.

At a **rank-20** residue, the Jacobian has a $6$-dimensional right kernel (giving $7^6 = 117{,}649$ first-order lifts modulo $49$) and a $4$-dimensional left kernel. A first-order lift extends to modulus $343$ if and only if the mod-$49$ residual—divided by $49$—vanishes when projected onto that $4$-dimensional left kernel. This yields **four quadratic equations** in the six free mod-$7$ digits.

[quartic_first_lifts.py](quartic_first_lifts.py) derives these four quadratics directly from the polynomial identity and verifies an explicit second lift by direct multiplication for every surviving choice.

* **Pilot verification:** Across the $6$ pilot triples, $98$ of the $117{,}649$ first lifts extend, and each of those $98$ admits $117{,}649$ second extensions, yielding **69,177,612** triples modulo $343$. On one representative, [QuarticLift.lean](QuarticLift.lean) proves in Lean that the four obstruction equations leave two digits free, restrict a third to $\{1, -1\}$, and uniquely determine the remaining three.
* **Totals across all 66 mod-7 residues:**
  * The $2$ rank-$20$ orbits of size $3$ have $49$ extendible first lifts per residue.
  * The $7$ rank-$20$ orbits of size $6$ have $98$ extendible first lifts per residue.
  * Each of the $18$ rank-$24$ residues has $49$ first lifts, and each of those has $49$ extensions.
  * Combined, there are **518,875,308** triples modulo $343$.

### Every residue lifts all the way to $\mathbb{Z}_7$

At every surviving rank-$20$ first lift, the four projected quadratics have Jacobian rank $4$ in the six free digits. To see why this guarantees lifts to arbitrary $7$-adic precision, parameterize the coefficient vector around a base first lift as
$$
\text{base lift} + 7Ku + 49v,
$$
where the columns of $K$ lift a basis of the first Jacobian kernel. As a polynomial in $(u, v)$, every coefficient equation is divisible by $49$. After dividing through by $49$:

* the derivative with respect to $v$ spans the original rank-$20$ image, and
* the derivative with respect to $u$ has rank $4$ in its cokernel.

Thus the combined derivative has full rank $24$. Multivariate Hensel lifting therefore applies, proving that **every one of the 66 residue classes lifts to $\mathbb{Z}_7$**.

## Searching for rational models

Since $7$-adic obstructions vanish, we examine whether any of these $7$-adic lifts can be rational polynomials—first by ruling out two structured families unconditionally, and then by running two large bounded searches.

### 1. Ruling out the sparse rank-20 family

Over $\mathbb{F}_7$, all $9$ rank-$20$ orbits follow the sparse pattern
$$
x = 3s^4, \qquad y = 1 + 3s^3, \qquad z = 1 - 2s^3 + 2s^6, \qquad s = \frac{ct + dt^2}{L}.
$$
In [QuarticSparse.lean](QuarticSparse.lean), Lean rules out even the broader rational family
$$
x = bs + as^4, \qquad y = 1 + cs^3, \qquad z = 1 + fs^3 + es^6
$$
(other than the constant seed):

* If $b \ne 0$, rescaling $s$ to set $b = 1$ forces $c$ to be a root of
  $$
  175616c^9 - 1153260c^8 + 1366848c^7 + 230592c^6 - 112896c^5 + 19548c^4 + 4704c^3 + 288c^2 + 1,
  $$
  whose homogenization has no root modulo $11$.
* If $b = 0$, the coefficient equations yield a contradiction directly.

*(Lifts whose rational coordinates depart from this sparse shape remain possible.)*

### 2. Ruling out pole-order-$\le 2$ lifts of the unique pole-2 orbit

For the single orbit where the reduced $y$ has pole order $2$, **no rational lift can keep $y$ at pole order $2$ or less.**

1. Write $Y = LE$. Modulo $7$, the triple is the pullback of a pole-$(2, 1, 3)$ triple along the Pell doubling map $t \mapsto 2t/(1 + 3t^2)$.
2. As checked in [search_quartic_pell.py](search_quartic_pell.py), both the upstairs and downstairs restricted Jacobians have determinant $2 \pmod 7$ at the representatives.
3. Hensel existence downstairs combined with Hensel uniqueness upstairs forces any such $7$-adic lift to be a pullback along the doubling map.
4. From a rational upstairs lift, the downstairs coefficients are recovered over $\mathbb{Q}$ via a triangular linear system with nonzero diagonal entries $2^i$.

Thus a rational lift with $y$ of pole order at most $2$ would yield a rational pole-order-$2$ Pell substitution, contradicting [pole_two.md](pole_two.md). *(A lift whose $y$ genuinely has pole order $3$ over $\mathbb{Q}$ but drops to order $2$ modulo $7$ remains open.)*

### 3. Bounded search: bounding $x$ alone

[quartic_rational_search.py](quartic_rational_search.py) writes the eight nonconstant coefficients of $x$ as $a_i/d$ in lowest common terms, in two separate coordinate systems:

* the **numerator basis** of $X(t)$, and
* the **Pell basis** $(u - 1)^i$ ($1 \le i \le 4$) and $v(u - 1)^j$ ($0 \le j \le 3$).

Why does bounding only $x$ suffice, with no denominator bound on $Y$ or $Z$? At any odd prime where $X$ is integral, $2L^{12} - X^3 = Z(Z + Y^2)$ is integral while both factors $Z$ and $Z + Y^2$ have constant term $1$ or $2$ (units at odd primes). Multiplicativity of the Gauss norm (the maximum $p$-adic size of a polynomial's coefficients) forces $Z$, $Z + Y^2$, and hence $Y$ to be integral at that prime as well.

Two ranges are exhausted:

* **Height $\max(d, |a_1|, \ldots, |a_8|) \le 8$:** The mod-$7$ filter leaves **657,962** numerator-basis vectors and **625,523** Pell-basis vectors. None admits rational $Y, Z$ of any height.
* **Height $\le 24$ with $\gcd(d, 35) = 1$:** Using the Chinese remainder theorem on mod-$5$ and mod-$7$ residues leaves **1,491,351** numerator-basis candidates and **1,520,489** Pell-basis candidates. Additional prime filters prune these to **11** and **15** vectors for exact factorization over $\mathbb{Q}$, and none yields a square.

### 4. Bounded search: fixing two coefficients of $Y$

In each of the three rank-$24$ orbit representatives, dropping the $Y_1$ and $Y_2$ columns from the Jacobian leaves an invertible $24 \times 24$ minor. Consequently, choosing rational values for $(Y_1, Y_2)$ determines a unique $7$-adic lift.

* Each coefficient has $91$ rational values of height at most $24$ matching its mod-$7$ residue, giving $3 \times 91^2 = 24{,}843$ pairs across the three representatives.
* [quartic_rational_slices.py](quartic_rational_slices.py) lifts every pair to precision $7^{64}$ and tests rational reconstruction. No triple has all coefficients of $Y$ and $Z$ reconstructing with numerator and denominator at most $10^{26}$ in absolute value.
* Because cube-root twists fix $Y$ and $Z$ and the reflection $t \mapsto -t$ preserves height bounds, this covers all **18** rank-$24$ residue triples.

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
