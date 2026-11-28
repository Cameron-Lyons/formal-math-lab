# Cubic Pell substitutions at 13

How high must the degree of a Pell substitution be to trace a nonconstant curve on $x^3 + y^2 z + z^2 = 2$ passing through the integer seed $(0, 1, 1)$? This note uses prime $13$ to prove that **linear, quadratic, and cubic Pell substitutions are all impossible**:

> **Main theorem (marked seed $(0, 1, 1)$).** For **every** nonsquare rational number $D$, any nonconstant polynomial substitution on $u^2 - Dv^2 = 1$ through $(0, 1, 1)$ must have $x$ of pole order at least $4$ at each of the two points at infinity.

The proof checks both orientations for the smaller cubic factor of $2 - x^3$; see the [argument for the marked point](#marked-seed) below.

More generally, suppose three rational functions on a pointed Pell conic satisfy $x^3 + y^2 z + z^2 = 2$, take integer values at the marked rational point, and have poles only at the two ends of the conic, each of order at most $3$ (this covers every polynomial map of total degree at most $3$ in the coordinates of $u^2 - Dv^2 = 1$). Then:

* **Ramified case ($v_{13}(D)$ odd):** The map is automatically constant — for **every** integral seed and every nonzero rational $D$ with odd $13$-adic valuation.
* **Split case ($D$ a square in $\mathbb{Q}_{13}$):** If the map is nonconstant, its reduction in the split Laurent coordinate is integral at $13$ and nonconstant.

## Why prime 13 works so well

Over $\mathbb{Q}_{13}$, any nonsquare discriminant $D$ falls into one of three local regimes:

1. **Ramified ($v_{13}(D)$ odd):** $K = \mathbb{Q}_{13}(\sqrt{D})$ still has residue field $\mathbb{F}_{13}$, and its Galois involution $\sigma$ acts *trivially* modulo $13$, collapsing symmetric Laurent polynomials into ordinary polynomials in $s = q + q^{-1}$ of degree at most $3$.
2. **Split ($D$ a square in $\mathbb{Q}_{13}$, represented locally by $d = 3$, since $4^2 \equiv 3 \pmod{13}$):** Both points at infinity are $\mathbb{Q}_{13}$-rational, and the Laurent coordinate $q = u + \sqrt{D}\,v$ lives directly over $\mathbb{Q}_{13}$.
3. **Unramified nonsplit / inert ($v_{13}(D)$ even, $D$ nonsquare in $\mathbb{Q}_{13}$, represented locally by $d = 2$):** The splitting field has residue field $\mathbb{F}_{169}$.

The engine behind all three cases is an exhaustive finite-field check: over $\mathbb{F}_{13}[t]$, there are **no** nonconstant ordinary polynomial solutions with all three coordinates of degree at most $6$. As soon as we have that, two $13$-adic rescalings (one near the mark $q = 1$, one zooming toward $q = \infty$) force every Laurent coefficient to be integral at $13$ and prevent the reduction from collapsing to a constant. Both general statements below build on this finite-field check together with the written valuation arguments.

## Ordinary polynomial solutions modulo 13

> **Lemma.** Every solution in $\mathbb{F}_{13}[t]$ to $x^3 + y^2 z + z^2 = 2$ where **all three** coordinates have degree at most $6$ is constant. (When $\deg x \le 5$, the same holds with *no* degree bound on $y$ or $z$; see [OrdinaryPolynomial.md](OrdinaryPolynomial.md).)

To close the remaining degree-$6$ case $\deg x = 6$, set $z' = z + y^2$, so that

$$
zz' = 2 - x^3
$$

has degree $18$. Because $\deg z \le 6$ and $\deg z' = \deg(z + y^2) \le 12$, the only way their degrees can sum to $18$ is $\deg z = 6$ and $\deg z' = 12$.

We normalize $x$ using the symmetries of $\mathbb{F}_{13}[t]$:

* Shift $t$ to eliminate the $t^5$ coefficient of $x$ (possible because $6$ is invertible modulo $13$).
* Scaling $t$ by a nonzero scalar multiplies the leading coefficient by a $6$th power (which hits $\{\pm 1\}$ in $\mathbb{F}_{13}^\times$), and multiplying $x$ by a cube root of unity covers the cube-root cosets; together these leave just **two** representatives for the leading coefficient of $x$: $1$ and $2$.

The five lower coefficients are arbitrary, leaving $2 \cdot 13^5 = 742{,}586$ candidate polynomials $x$. For each one, [cubic_ordinary_at13.py](cubic_ordinary_at13.py) factors $2 - x^3$, lists all monic degree-$6$ divisors, and checks every nonzero scalar multiple $z$ to test whether $(2 - x^3)/z - z$ is a square in $\mathbb{F}_{13}[t]$. Across all $737{,}856$ monic divisors, there are **zero solutions**. The script also rechecks the degree-$5$ case by fixing the smaller cubic factor and varying $x$ modulo that factor.

## Integral Laurent coefficients

Let $K = \mathbb{Q}_{13}$ if $D$ is a square in $\mathbb{Q}_{13}$, or $K = \mathbb{Q}_{13}(\sqrt{D})$ if $v_{13}(D)$ is odd. In both cases, the residue field of $K$ is $\mathbb{F}_{13}$.

Introduce the Laurent coordinate $q = u + \sqrt{D}\,v$, which puts the two ends of the conic at $q = 0$ and $q = \infty$. Multiplying $q$ by the inverse of the marked point normalizes the mark to $q = 1$, so each coordinate $f \in \{x, y, z\}$ takes the form

$$
f(q) = \sum_{i=-3}^3 a_i q^i.
$$

Two valuation-balancing zooms now pin down the coefficients $a_i$:

1. **Integrality (zooming near the mark $q = 1$):** Set $q = 1 + t$ and clear denominators to write $f(1 + t) = A_f(t)/(1 + t)^3$. Each numerator $A_f$ has degree at most $6$ and an integral constant term (the marked value). Suppose some coefficient of $A_x, A_y, A_z$ has negative valuation, and let

   $$
   h = \max_{f,\, i > 0} \left(-\frac{v([t^i]A_f)}{i}\right) > 0.
   $$

   Pick $\lambda$ of valuation $h$ in a totally ramified extension and substitute $t = \lambda T$. All three numerators become integral, at least one positive-degree coefficient stays a unit, and the denominator $(1 + \lambda T)^3$ reduces to $1$. Reducing modulo the maximal ideal yields a nonconstant ordinary polynomial solution over $\mathbb{F}_{13}$ with all degrees at most $6$ — contradicting the lemma above. Hence every $A_f$ is integral, and shifting back via $t = q - 1$ shows every Laurent coefficient $a_i$ is integral.
2. **Nonconstant reduction (zooming toward infinity):** Next, suppose the map is nonconstant yet all three Laurent reductions are constant — meaning every $a_i$ with $i \ne 0$ has positive valuation. Swap $q$ and $q^{-1}$ if needed so that some positive-index coefficient is nonzero, and set

   $$
   r = \min_{f,\, i > 0} \frac{v(a_i)}{i} > 0
   $$

   over all nonzero positive-index coefficients of $x, y, z$. In a totally ramified extension, pick $\mu$ with $v(\mu) = r$ and set $q = \mu^{-1} T$. On reduction, every negative power $a_{-i} \mu^i T^{-i}$ vanishes while at least one positive power $a_i \mu^{-i} T^i$ survives, producing a nonconstant ordinary polynomial solution over $\mathbb{F}_{13}$ of degree at most $3$. That is again impossible, so any nonconstant map has a **nonconstant** Laurent reduction.

## Ramified quadratic case

Now suppose $v_{13}(D)$ is odd. The nontrivial automorphism $\sigma$ of $K/\mathbb{Q}_{13}$ swaps $q$ and $q^{-1}$ (this still holds after shifting the mark to $q = 1$, because the mark has norm $1$), so rationality of $f$ gives $a_{-i} = \sigma(a_i)$. Because $K/\mathbb{Q}_{13}$ is totally ramified, $\sigma$ acts **trivially** on the residue field $\mathbb{F}_{13}$, meaning $\bar a_{-i} = \bar a_i$.

Every reduced coordinate $\bar f(q) = \bar a_0 + \sum_{i=1}^3 \bar a_i(q^i + q^{-i})$ is therefore a polynomial of degree at most $3$ in the single symmetric variable

$$
s = q + q^{-1},
$$

since each $q^i + q^{-i}$ ($i > 0$) is a monic degree-$i$ polynomial in $s$ (for instance, $q^2 + q^{-2} = s^2 - 2$ and $q^3 + q^{-3} = s^3 - 3s$). Because $s$ is transcendental over $\mathbb{F}_{13}$, these three polynomials in $s$ satisfy the surface equation identically over $\mathbb{F}_{13}$. By our finite-field lemma, they must be constant — and by the second rescaling step above, a constant Laurent reduction forces the original map itself to be constant.

## Quadratic $x$ and a cubic factor

A related obstruction has its own end-to-end Lean proof in [QuarticFactorPencil.lean](QuarticFactorPencil.lean). Write $\alpha = \sqrt[3]{2}$. Suppose $x(s) \in \mathbb{Q}[s]$ is quadratic and $z(s)$ is a cubic factor of $2 - x(s)^3$. Then $z(s)$ is irreducible over $\mathbb{Q}$ (a rational root would give a rational cube root of $2$), so any root $\theta$ of $z$ generates $\mathbb{Q}(\alpha)$ with $x(\theta) = \alpha$.

Shift $s$ so that $\theta = a\alpha + b\alpha^2$ (with $a, b \in \mathbb{Q}$ not both zero) and put $d = a^3 - 2b^3$. Then:

* the monic minimal polynomial of $\theta$ is $P(s) = s^3 - 6abs - 2a^3 - 4b^3$;
* the quadratic $G(s) = a^2 s - bs^2 + 4ab^2$ satisfies $G(\theta) = d\alpha$, so $x = G/d$.

Writing $z = uP$ ($u \in \mathbb{Q}^\times$) and $Q = (2d^3 - G^3)/P$, the surface equation becomes the cubic pencil

$$
u d^3 y^2 = Q - d^3 u^2 P.
$$

Lean proves that for all rational $a, b$ not both zero and every $u \ne 0$, the cubic on the right-hand side has **nonzero discriminant**. When its leading cubic term cancels, Lean rules out an integral point using the tangent relation to $V^2 = U^3 - 2$. Neither a repeated root nor leading-term cancellation in this pencil can produce an integral Pell family. The Lean proof pairs the complementary scalars $u$ and $b^3/(d^3 u)$, establishes a projective obstruction modulo $13$, and descends on their common denominator.

To reproduce the ordinary finite-field computation above, run:

```sh
uv run --with python-flint==0.9.0 cubic_ordinary_at13.py
```

<a id="marked-seed"></a>

## All Pell discriminants through the seed $(0,1,1)$

Let $D$ be any nonsquare rational number, and consider a map from a pointed Pell conic of discriminant $D$ that is regular away from its two ends and sends the marked rational point to $(0, 1, 1)$. **If $x$ has pole order at most $3$ at each end, the entire map is constant.** Lean checks the algebraic obstructions, while the finite-field enumerations and local coordinate changes are verified separately as described below.

### Step 1: Reduction to pole order 3 and even $v_{13}(D)$

* **Pole orders $1$ and $2$** are already ruled out in [pole_two.md](pole_two.md).
* **Pole order $3$:** [PoleOne.lean](PoleOne.lean) shows that $y$ also has pole order $3$ and that $z$ and $z + y^2$ have pole orders $3$ and $6$ in some order. Applying the surface involution $z \mapsto -z - y^2$ if needed, we may assume $z$ has pole order $3$. That maps the marked value $(0, 1, 1)$ to either $(0, 1, 1)$ or $(0, 1, -2)$.
* **Odd $v_{13}(D)$:** Already ruled out in the ramified section above.

### Step 2: Local $t$-chart integrality and nonconstancy (even $v_{13}(D)$)

When $v_{13}(D)$ is even, let $d = 3$ if $D$ is a square in $\mathbb{Q}_{13}$ (split) and $d = 2$ otherwise (inert); these represent the two unit square classes in $\mathbb{Q}_{13}^\times$. After a local change of variable and shifting the mark, the conic becomes $u^2 - dv^2 = 1$ with the mark at $(1, 0)$. Setting $L = 1 - dt^2$, all three coordinates share the denominator $L^3$ with numerators $X, Y, Z$ of degree at most $6$.

* **Integrality at $13$:** Every numerator coefficient is $13$-integral; otherwise, balancing in the $t$-chart would yield a nonconstant ordinary polynomial solution over $\mathbb{F}_{13}$ with all degrees at most $6$ (since the balanced denominator reduces to $1$), contradicting our lemma.
* **Nonconstant reduction in the inert case ($d = 2$):** In the split case ($d = 3$), nonconstancy was already proved above. For $d = 2$, pass to the unramified quadratic splitting field and set $q = (1 + \sqrt{d}\,t)/(1 - \sqrt{d}\,t)$. Because $2\sqrt{d}$ is a unit, converting between $t$-numerators over $L^3$ and Laurent coefficients in $q$ is integral in both directions. If the reduction were constant, dilating $q$ toward infinity as before would produce a nonconstant ordinary polynomial solution of degree at most $3$ in each coordinate over $\mathbb{F}_{169}$ taking the marked value modulo $13$ at $T = 0$ (since every nonconstant Laurent coefficient has positive valuation). For both seeds $(0, 1, 1)$ and $(0, 1, -2)$, [cubic_seed13.py](cubic_seed13.py) rules this out by normalizing the first nonzero coefficient of $x$ and factoring $2 - x^3$: there are $28{,}561$, $338$, and $1$ candidates for first exponents $1$, $2$, and $3$, and none works. (A constant $x$ at either seed equals $0$, forcing $z(z + y^2) = 2$ and making $y, z$ constant as well.)

### Step 3: Exhaustive search over $\mathbb{F}_{13}$ and elimination of all 7 surviving orbits

That leaves nonconstant reductions of

$$
X^3 + ZY^2 + Z^2 L^3 = 2L^9
$$

over $\mathbb{F}_{13}$. Both symmetries $X \mapsto \zeta X$ ($\zeta^3 = 1$) and $t \mapsto -t$ preserve either seed. For each $d \in \{2, 3\}$, there are $804{,}835$ lexicographically normalized candidate numerators $X$. For each candidate, [cubic_seed13.py](cubic_seed13.py) factors $2L^9 - X^3$, tests every divisor $Z$ of degree at most $6$ with the required constant term, and checks whether $(2L^9 - X^3)/Z - ZL^3$ is a square polynomial of degree at most $12$. (Each row also contains one constant orbit, already excluded.)

| $d$ | Marked $z$ | Nonconstant orbits | Orbits excluded at a simple root of $L$ | Orbits excluded modulo $13^2$ |
| --- | --- | --- | --- | --- |
| 2 | 1 | 1 | 1 | 0 |
| 2 | -2 | 1 | 1 | 0 |
| 3 | 1 | 2 | 2 | 0 |
| 3 | -2 | 3 | 2 | 1 |

Every surviving nonconstant orbit is ruled out by one of two obstructions:

1. **Simple-root pole drop ($6$ of the $7$ orbits):** Every orbit in the simple-root column has a root of $L$ (in $\mathbb{F}_{13}$ or $\mathbb{F}_{169}$) where $X$ vanishes to order $1$, $Y$ vanishes to order at least $2$, and $Z$ is a unit. By the local rescaling theorem in [CubicSimplePole.md](CubicSimplePole.md), such an orbit cannot preserve the order-$3$ pole of $x$ (this works in either residue field, and a local coordinate change preserves the two geometric ends, where a rational $x$ on a nonsplit conic has the same pole order).
2. **Mod-$13^2$ lift obstruction ($1$ remaining orbit: $d = 3$, $z = -2$):** For this single orbit, a left-kernel vector of the $18$ first-order correction equations pairs to $4 \not\equiv 0$ with the right-hand side in $\mathbb{F}_{13}$. This calculation uses the exact marked value $z = -2$, which is preserved by both $t \mapsto -t$ and cube-root twists of $X$ when lifted to the local field. See [CubicSeed13Lift.lean](CubicSeed13Lift.lean) for the Lean certificate and [cubic_seed13.py](cubic_seed13.py) for the exhaustive field checks.

Reproduce the seed computations with:

```sh
uv run --with python-flint==0.9.0 cubic_seed13.py
```
