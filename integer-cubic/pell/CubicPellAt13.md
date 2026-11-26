# Cubic Pell substitutions at 13

For every nonsquare rational $D$, any nonconstant polynomial substitution on $u^2 - Dv^2 = 1$ through $(0, 1, 1)$ must have $x$ of pole order at least 4 at each of the two points at infinity. The proof checks both choices for the smaller cubic factor of $2 - x^3$. See the [argument for the marked point](#marked-seed) below.

More generally, suppose three rational functions on a pointed Pell conic satisfy $x^3 + y^2 z + z^2 = 2$ and take integer values at the marked rational point. Suppose each coordinate has poles only at the two ends, with pole order at most 3 at each end. (This includes any polynomial map of total degree at most 3 in the coordinates of $u^2 - Dv^2 = 1$.) Then:

* If $v_{13}(D)$ is odd, the map is constant.
* If $D$ is a square in $\mathbb{Q}_{13}$ and the map is nonconstant, its reduction in the split Laurent coordinate is integral and nonconstant.

The first statement holds for every integral seed and every nonzero rational $D$ with odd 13-adic valuation. Both statements build on the finite-field check below, together with the written valuation arguments.

## Ordinary polynomial solutions modulo 13

Every solution in $\mathbb{F}_{13}[t]$ where **all three** coordinates have degree at most 6 is constant. When $\deg x \le 5$, the same holds with no degree bound on $y$ or $z$; see [OrdinaryPolynomial.md](OrdinaryPolynomial.md).

For $\deg x = 6$, set $z' = z + y^2$. Then $zz' = 2 - x^3$ has degree 18. Since $\deg z' \le 12$ and $\deg z \le 6$, their degrees must be exactly 12 and 6. Shift $t$ to kill the degree-5 coefficient of $x$. Scaling $t$ by a unit and multiplying $x$ by a cube root of unity leaves just two representatives for the leading coefficient of $x$: 1 and 2.

The five lower coefficients are free, giving $2 \cdot 13^5 = 742{,}586$ candidate polynomials. For each one, [cubic_ordinary_at13.py](cubic_ordinary_at13.py) factors $2 - x^3$, lists all monic degree-6 divisors, and checks every scalar multiple $z$ to see whether $(2 - x^3)/z - z$ is a square. Across all 737,856 monic divisors, there are no solutions. The script also rechecks the degree-5 case by fixing the smaller cubic factor and varying $x$ modulo that factor.

## Integral Laurent coefficients

Let $K = \mathbb{Q}_{13}$ if $D$ is a square in $\mathbb{Q}_{13}$, or $K = \mathbb{Q}_{13}(\sqrt{D})$ if $v_{13}(D)$ is odd. In either case the residue field is $\mathbb{F}_{13}$. The Laurent coordinate $q = u + \sqrt{D}\,v$ places the two poles at 0 and $\infty$. Multiplying by the inverse of the marked point normalizes $q = 1$ at the mark, so each coordinate has the form $f(q) = \sum_{i=-3}^3 a_i q^i$.

Rewrite $f(1 + t) = A_f(t)/(1 + t)^3$. Each numerator $A_f$ has degree at most 6 and an integral constant term. Suppose some coefficient has negative valuation, and let $h > 0$ be the maximum of $-v([t^i]A_f)/i$ over all nonzero positive-degree terms of the three numerators. Pick $\lambda$ of valuation $h$ in a totally ramified extension and substitute $t = \lambda T$. The numerators become integral, at least one nonconstant coefficient stays a unit, and the denominator reduces to 1. This produces a nonconstant ordinary solution over $\mathbb{F}_{13}$ with all degrees at most 6, which we just ruled out. So every $A_f$ is integral, and shifting back via $t = q - 1$ shows all Laurent coefficients $a_i$ are integral.

Next, suppose the three Laurent reductions were all constant, meaning every $a_i$ with $i \ne 0$ has positive valuation. For a nonconstant map, swap $q$ and $q^{-1}$ if needed so that some positive-index coefficient is nonzero. Let $r > 0$ be the minimum of $v(a_i)/i$ over all positive-index coefficients in the three functions. In a totally ramified extension, pick $\mu$ with $v(\mu) = r$ and set $q = \mu^{-1} T$. On reduction, all negative powers vanish while at least one positive power survives, giving a nonconstant ordinary solution over $\mathbb{F}_{13}$ of degree at most 3. That is impossible, so any nonconstant map has a nonconstant Laurent reduction.

## Ramified quadratic case

When $v_{13}(D)$ is odd, the nontrivial automorphism $\sigma$ of $K/\mathbb{Q}_{13}$ swaps $q$ and $q^{-1}$ (even after shifting by the marked point), so $a_{-i} = \sigma(a_i)$. Because the extension is totally ramified, $\sigma$ acts trivially on the residue field.

The reduced functions are therefore polynomials of degree at most 3 in $s = q + q^{-1}$, because each $q^i + q^{-i}$ ($i > 0$) is a monic degree-$i$ polynomial in $s$. Since $s$ is transcendental, these reduced polynomials satisfy the surface equation identically over $\mathbb{F}_{13}$. The finite-field result forces them to be constant, and the rescaling step above then forces the original map to be constant.

## Quadratic x and a cubic factor

A related obstruction has its own end-to-end Lean proof in [QuarticFactorPencil.lean](QuarticFactorPencil.lean). Write $\alpha^3 = 2$. If $x(s)$ is quadratic, any cubic factor $z(s)$ of $2 - x(s)^3$ is irreducible over $\mathbb{Q}$, since a rational root would give a rational cube root of 2. A root $\theta$ of $z$ generates $\mathbb{Q}(\alpha)$ with $x(\theta) = \alpha$.

Shift $s$ so that $\theta = a\alpha + b\alpha^2$, and put $d = a^3 - 2b^3$. The monic minimal polynomial of $\theta$ is $P = s^3 - 6abs - 2a^3 - 4b^3$, and the quadratic $G = a^2 s - bs^2 + 4ab^2$ satisfies $G(\theta) = d\alpha$, so $x = G/d$. Writing $z = uP$ and $Q = (2d^3 - G^3)/P$, the surface equation becomes

$$
u d^3 y^2 = Q - d^3 u^2 P.
$$

Lean proves that for all rational $a, b$ not both zero and every $u \ne 0$, the cubic on the right has nonzero discriminant. When its cubic term cancels, Lean rules out an integral point using the tangent relation to $V^2 = U^3 - 2$. Neither a repeated root nor leading-term cancellation in this pencil can produce an integral Pell family. The Lean proof pairs the complementary scalars $u$ and $b^3/(d^3 u)$, proves a projective obstruction modulo 13, and descends on their common denominator.

To reproduce the finite-field computation above, run:

```sh
uv run --with python-flint==0.9.0 cubic_ordinary_at13.py
```

<a id="marked-seed"></a>

## All Pell discriminants through the seed $(0,1,1)$

Let $D$ be any nonsquare rational number, and consider a map from a pointed Pell conic of discriminant $D$ that is regular away from its two ends and sends the marked rational point to $(0, 1, 1)$. **If $x$ has pole order at most 3 at each end, the entire map is constant.** Lean checks the algebraic obstructions, while the finite-field enumerations and local coordinate changes are verified separately as described below.

Pole orders 1 and 2 are already ruled out in [pole_two.md](pole_two.md). At pole order 3, [PoleOne.lean](PoleOne.lean) shows that $y$ has order 3 and that $z$ and $z + y^2$ have orders 3 and 6 in some order. Using the involution $z \mapsto -z - y^2$, we can take $z$ to have order 3. That puts the marked value at either $(0, 1, 1)$ or $(0, 1, -2)$.

The case of odd $v_{13}(D)$ is already proved above. When $v_{13}(D)$ is even, let $d = 3$ if $D$ is a square in $\mathbb{Q}_{13}$ and $d = 2$ otherwise; these represent the two unit square classes. After a local change of variable and shifting the mark, the conic is $u^2 - dv^2 = 1$ with the mark at $(1, 0)$. With $L = 1 - dt^2$, all three coordinates share the denominator $L^3$ with numerator degrees at most 6. All numerator coefficients are integral at 13, because otherwise the balancing argument in the $t$-chart would yield a nonconstant ordinary polynomial solution over $\mathbb{F}_{13}$ with all degrees at most 6 (the balanced denominator reduces to 1).

In the unramified nonsplit case ($d = 2$), we also have to rule out a constant reduction. Over the unramified quadratic splitting field, set $q = (1 + \sqrt{d}\,t)/(1 - \sqrt{d}\,t)$. Converting between $t$-numerators over $L^3$ and Laurent coefficients in $q$ is integral in both directions since $2\sqrt{d}$ is a unit. If the reduction were constant, dilating $q$ as before would produce a nonconstant ordinary polynomial solution of degree at most 3 in each coordinate over $\mathbb{F}_{169}$, taking the marked value modulo 13 at $T = 0$ (since every nonconstant Laurent coefficient has positive valuation). For both seeds, [cubic_seed13.py](cubic_seed13.py) rules this out by normalizing the first nonzero coefficient of $x$ and factoring $2 - x^3$: there are 28,561, 338, and 1 candidates for first exponents 1, 2, and 3, and none works. A constant $x$ at either seed is 0, which forces $z(z + y^2) = 2$ and makes $y, z$ constant too.

That leaves nonconstant reductions of $X^3 + ZY^2 + Z^2 L^3 = 2L^9$ over $\mathbb{F}_{13}$. Multiplying $X$ by a cube root of unity and negating $t$ both preserve either seed. For each $d$, there are 804,835 lexicographically normalized candidate numerators $X$. For each one, [cubic_seed13.py](cubic_seed13.py) factors $2L^9 - X^3$, checks all divisors $Z$ of degree at most 6 with the required constant term, and tests whether $(2L^9 - X^3)/Z - ZL^3$ is a square polynomial of degree at most 12. Each row also has one constant orbit, which is already excluded.

| $d$ | Marked $z$ | Nonconstant orbits | Orbits excluded at a simple root of $L$ | Orbits excluded modulo $13^2$ |
| --- | --- | --- | --- | --- |
| 2 | 1 | 1 | 1 | 0 |
| 2 | -2 | 1 | 1 | 0 |
| 3 | 1 | 2 | 2 | 0 |
| 3 | -2 | 3 | 2 | 1 |

Every orbit in the simple-root column has a root of $L$ where $X$ vanishes to order 1, $Y$ vanishes to order at least 2, and $Z$ is a unit. The local rescaling argument in [CubicSimplePole.md](CubicSimplePole.md) shows that such an orbit cannot keep the order-3 pole of $x$ (this works in either residue field, and a local coordinate change preserves the two geometric ends, where a rational $x$ on a nonsplit conic has the same pole order).

For the single remaining orbit in the last column ($d = 3$, $z = -2$), a left-kernel vector of the 18 first-correction equations pairs to 4 with the right-hand side in $\mathbb{F}_{13}$. This calculation uses the exact marked value $z = -2$, which is preserved by both $t \mapsto -t$ and cube-root twists of $X$ when lifted to the local field. See [CubicSeed13Lift.lean](CubicSeed13Lift.lean) for the Lean certificate and [cubic_seed13.py](cubic_seed13.py) for the exhaustive field checks.

Reproduce the seed computations with:

```sh
uv run --with python-flint==0.9.0 cubic_seed13.py
```
