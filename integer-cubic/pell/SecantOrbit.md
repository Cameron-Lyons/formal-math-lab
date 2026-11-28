# Chords and tangents through the eight small points

On a smooth cubic surface such as $z^2 + y^2 z + x^3 = 2$, the classical geometric way to generate new points from known ones is the **chord-and-tangent method**: draw a line joining two known points, a tangent line at a known point, or a line from a known point to a rational point at infinity, and read off the third intersection point with the surface.

Starting from $(0, 1, 1)$, elementary axis-parallel chords and a single line to infinity reach a cluster $S$ of **eight small integer points**:
$$
(0, \pm 1, 1), \qquad (0, \pm 1, -2), \qquad (-7, \pm 8, 5), \qquad (-7, \pm 8, -69).
$$
Here we prove that **$S$ is completely closed under single-step integral secant and tangent operations**: every chord between two points of $S$, every line from a point of $S$ to a rational point at infinity, and every tangent line at a point of $S$ whose third intersection is an integer point lands back inside $S$.

## How the eight points connect

Starting at $(0, 1, 1)$:

* Vertical chords send $z \mapsto -y^2 - z$, moving $(0, 1, 1)$ to $(0, 1, -2)$.
* The line $(0, 1, -2) + t(-1, 1, 1)$ (heading to a rational point at infinity) reaches $(-7, 8, 5)$ at $t = 7$.
* Applying vertical chords ($z \mapsto -y^2 - z$) and horizontal $y$-chords ($y \mapsto -y$) generates all eight points of $S$.

Because the reflection $y \mapsto -y$ preserves lines and $S$, it suffices to inspect the four representatives with $y > 0$. The table records every non-axis line to infinity and every tangent line that hits a second integer point (in all cases, that point already lies in $S$):

| Affine point | Non-axis lines to infinity giving a second integer point | Tangent lines giving a second integer point |
| --- | ---: | ---: |
| $(0, 1, 1)$ | 0 | 0 |
| $(0, 1, -2)$ | 1 | 0 |
| $(-7, 8, 5)$ | 1 | 0 |
| $(-7, 8, -69)$ | 0 | 0 |

## Turning line geometry into Thue equations

### Setup for an arbitrary primitive direction

Fix an integer point $P = (x, y, z) \in S$ and a primitive integer direction vector $D = (i, j, k)$. Restricting $z^2 + y^2 z + x^3 - 2$ to the line $P + tD$ produces the cubic $t(L + tQ + t^2 C)$, where
$$
L = 3x^2 i + 2yzj + (y^2 + 2z)k, \qquad
Q = 3xi^2 + zj^2 + 2yjk + k^2, \qquad
C = i^3 + j^2 k.
$$
Because $D$ is primitive, Bézout's identity guarantees that any second integer point on the line occurs at an **integer** value of $t$.

### The three classes of lines

1. **Chords between two distinct points of $S$:** Write $P' = P + hD$ with $D$ primitive. Whenever $C \ne 0$, the product of the two roots of $L + tQ + t^2 C$ places the third intersection at $t = L/(hC)$. The script checks all $\binom{8}{2} = 28$ pairs directly.
2. **Lines to a rational point at infinity ($C = 0$):** When $j \ne 0$, setting $m/n = -i/j$ forces $k/j = (m/n)^3$, so up to sign the primitive directions are $(-n^2 m, n^3, m^3)$ for coprime integers $m, n$ (the case $j = 0$ is the vertical axis). When $Q \ne 0$, a second integer point occurs at $t = -L/Q$, requiring the divisibility $Q \mid L$. Here $F = Q$ is a binary sextic and $G = L$ is a binary cubic.
3. **Tangent lines at $P$ ($L = 0$):** Express $D$ in an integral basis of $\ker L$ with coprime integer coordinates $(m, n)$. When $C \ne 0$, the third intersection occurs at $t = -Q/C$, requiring the divisibility $C \mid Q$. Here $F = C$ is a binary cubic and $G = Q$ is a binary quadratic.

### Bounding $|F(m, n)|$ via resultants

The one exceptional sextic—lines to infinity from $(0, 1, 1)$—is handled directly in Lean by `seed_secant`, which forces $t n^2 m = 0$. Every other denominator form $F$ has full degree in $m$ and is irreducible over $\mathbb{Q}$, so none vanishes at a primitive integer pair.

Whenever $F(m, n) \mid G(m, n)$ for coprime $(m, n)$, every prime power dividing $F(m, n)$ must divide one of the two dehomogenized resultants:

* For primes not dividing $n$, evaluate the Bézout identity for $F(X, 1)$ and $G(X, 1)$ at $m/n$.
* For primes dividing $n$, evaluate the Bézout identity for $F(1, X)$ and $G(1, X)$ at $n/m$.

Hence $|F(m, n)|$ divides the least common multiple of the two absolute resultants, reducing the divisibility condition to a finite list of Thue equations $F(m, n) = d$.

In the first six remaining cases, PARI/GP solves $F(m, n) = d$ for every surviving signed divisor $d$ using `thueinit(F(X,1),1)` (which requests unconditional certification) and `thue`, then checks each solution in exact arithmetic; see the [PARI `thue` documentation](https://pari.math.u-bordeaux.fr/dochtml/html/Polynomials_and_power_series.html#thue).

## The final tangent cubic at $(-7, 8, -69)$

At $(-7, 8, -69)$, the integral tangent basis yields the binary cubic
$$
f(X) = F(X, 1) = -213 X^3 + 39450 X^2 - 2430429 X + 49836032.
$$
Its resultant bound factors as $3^4 \cdot 23 \cdot 83 \cdot 347 \cdot 661090691$. Because negating $(m, n)$ flips the sign of $F$, we need only positive divisors $d$; exactly **27** of them survive the primitive-pair and divisibility checks modulo $9$.

Rather than running generic Thue solving against that large prime factor, we pass to the cubic number field and eliminate every norm representative modulo a small split prime:

1. **Norm equations in the cubic field.** Set $a = -213$ and let $\theta$ be a root of $a^2 f(X/a)$. Then $am - \theta n$ is an algebraic integer of norm $a^2 F(m, n)$. PARI/GP certifies the cubic field unconditionally via `bnfcertify` and computes all algebraic-integer norm representatives modulo positive-norm units via `bnfisintnorm`; see the [PARI number field documentation](https://pari.math.u-bordeaux.fr/dochtml/html/General_number_fields.html#bnfisintnorm). Across the $27$ right-hand sides there are **110** representatives in total; the field has unit rank $1$ and torsion $\{\pm 1\}$.
2. **Split-prime determinant obstruction.** Let $\beta$ be a norm representative and $u$ a fundamental unit. If $\pm \beta u^k = am - \theta n$, then modulo any split prime $q$ (where the defining cubic splits completely with roots $\theta_1, \theta_2, \theta_3 \bmod q$), the vector of three reductions of $\beta u^k$ must lie in $\operatorname{span}\{(1, 1, 1),\, (\theta_1, \theta_2, \theta_3)\}$. Writing that linear dependence as a vanishing $3 \times 3$ determinant gives
   $$
   (\theta_2 - \theta_3)\beta_1 u_1^k
   + (\theta_3 - \theta_1)\beta_2 u_2^k
   + (\theta_1 - \theta_2)\beta_3 u_3^k \equiv 0 \pmod q.
   $$
3. **Exhausting exponents modulo $q - 1$.** Checking every exponent $k \pmod{q - 1}$, the script finds a split prime $q \le 2000$ for every one of the $110$ representatives where no $k$ satisfies the congruence (restricted to primes where all compact factors reduce and invert cleanly).

This rules out every integral third tangent intersection at $(-7, 8, -69)$.

## Reproduction and trust boundary

Run:

```sh
lake -d .. env lean SecantOrbit.lean
gp -fq secant_orbit.gp
```

* **Lean** verifies the line identities, the exceptional sextic at $(0, 1, 1)$ (`seed_secant`), the cubic norm identity, the split-prime determinant relation, and the fact that the tangent-direction cubic at any integer point has no repeated root.
* **PARI/GP** executes the certified Thue solves, number-field norm enumerations, and finite congruence checks.
