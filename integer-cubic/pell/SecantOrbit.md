# Chords and tangents through the eight small points

Let $S$ be the set of eight small integer points on $z^2 + y^2 z + x^3 = 2$:

$$
(0, \pm 1, 1), \quad (0, \pm 1, -2), \quad (-7, \pm 8, 5), \quad (-7, \pm 8, -69).
$$

Starting from $(0, 1, 1)$, the vertical chord lands on $(0, 1, -2)$, and the line $(0, 1, -2) + t(-1, 1, 1)$ reaches $(-7, 8, 5)$ at $t = 7$. Vertical chords send $z \mapsto -y^2 - z$, and chords parallel to the $y$-axis send $y \mapsto -y$, reaching all eight points in $S$.

Conversely, if we take any chord between two points of $S$, any line from a point of $S$ to a rational point at infinity, or any tangent line at a point of $S$, every integral third intersection stays inside $S$. Thus $S$ is closed under single-step integral secant and tangent operations:

| Affine point | Non-axis lines to infinity giving a second integer point | Tangent lines giving a second integer point |
| --- | ---: | ---: |
| $(0, 1, 1)$ | 0 | 0 |
| $(0, 1, -2)$ | 1 | 0 |
| $(-7, 8, 5)$ | 1 | 0 |
| $(-7, 8, -69)$ | 0 | 0 |

## Exhausting the line directions

For an integer point $P = (x, y, z)$ and a primitive integer direction $D = (i, j, k)$, restricting $z^2 + y^2 z + x^3 - 2$ to the line $P + tD$ gives $t(L + tQ + t^2 C)$, where

$$
L = 3x^2 i + 2yzj + (y^2 + 2z)k, \quad
Q = 3xi^2 + zj^2 + 2yjk + k^2, \quad
C = i^3 + j^2 k.
$$

Because $D$ is primitive, Bézout's identity ensures that any second integer point on the line occurs at an integer value of $t$. Two types of lines yield divisibility conditions:

* A line to a rational point at infinity has $C = 0$. When $j \ne 0$, writing $m/n = -i/j$ forces $k/j = (m/n)^3$, so up to sign the primitive directions are $(-n^2 m, n^3, m^3)$ for coprime integers $m, n$. (The case $j = 0$ is the vertical axis.) A second integer point requires $Q \mid L$ whenever $Q \ne 0$.
* A tangent line at $P$ has $L = 0$. Express $D$ in an integral basis of $\ker L$ with coprime coordinates $m, n$. When $C \ne 0$, the third intersection is at $t = -Q/C$, so an integer point requires $C \mid Q$.

For lines to infinity, the script forms the binary sextic $F = Q$ and cubic $G = L$. For tangent lines, it forms the cubic $F = C$ and quadratic $G = Q$. The one exceptional sextic at $(0, 1, 1)$ is handled in Lean by `seed_secant`, which forces $t n^2 m = 0$. All other denominator forms $F$ have full degree in $m$ and are irreducible over $\mathbb{Q}$, so none vanishes at a primitive integer pair.

Whenever $F(m, n) \mid G(m, n)$, every prime power dividing $F(m, n)$ must divide one of the two dehomogenized resultants: evaluate the Bézout identity for $F(X, 1)$ and $G(X, 1)$ at $m/n$ for primes not dividing $n$, and use $F(1, X)$ and $G(1, X)$ at $n/m$ for primes dividing $n$. Therefore $|F(m, n)|$ divides the least common multiple of the two absolute resultants.

In the first six cases, PARI/GP solves $F(m, n) = d$ for every surviving signed divisor $d$ using `thueinit(F(X,1),1)` (which requests unconditional certification) and `thue`, then checks each solution in exact arithmetic; see the [PARI `thue` documentation](https://pari.math.u-bordeaux.fr/dochtml/html/Polynomials_and_power_series.html#thue).

Because $y \mapsto -y$ preserves lines, it is enough to check the four representatives with $y > 0$. For chords joining two distinct points $P$ and $P' = P + hD$ ($D$ primitive) of $S$, when $C \ne 0$ the product of the two roots of $L + tQ + t^2 C$ gives the third intersection at $t = L/(hC)$. The script checks all 28 pairs directly.

## The final tangent cubic

At $(-7, 8, -69)$, the integral tangent basis gives

$$
f(X) = F(X, 1) = -213 X^3 + 39450 X^2 - 2430429 X + 49836032.
$$

Its resultant bound factors as $3^4 \cdot 23 \cdot 83 \cdot 347 \cdot 661090691$. Since negating $(m, n)$ flips the sign of $F$, we only need positive divisors $d$; 27 of them pass the primitive-pair and divisibility checks modulo 9.

Put $a = -213$ and let $\theta$ be a root of $a^2 f(X/a)$. Then $am - \theta n$ is an algebraic integer of norm $a^2 F(m, n)$. PARI/GP certifies the cubic field unconditionally with `bnfcertify` and computes all norm representatives modulo positive-norm units with `bnfisintnorm`; see the [PARI number field documentation](https://pari.math.u-bordeaux.fr/dochtml/html/General_number_fields.html#bnfisintnorm). Across the 27 right-hand sides there are 110 representatives in total, and the field has unit rank 1 with torsion $\{\pm 1\}$.

Let $\beta$ be a norm representative and $u$ a fundamental unit. If $\pm \beta u^k = am - \theta n$, then modulo any split prime $q$, the vector of its three reductions lies in the span of $(1, 1, 1)$ and $(\theta_1, \theta_2, \theta_3)$, giving the determinant test

$$
(\theta_2 - \theta_3)\beta_1 u_1^k
+ (\theta_3 - \theta_1)\beta_2 u_2^k
+ (\theta_1 - \theta_2)\beta_3 u_3^k \equiv 0 \pmod q.
$$

Testing all $k$ modulo $q - 1$, the script finds a split prime $q \le 2000$ for every one of the 110 representatives where no exponent $k$ satisfies the congruence (using only primes where all compact factors reduce and invert cleanly). This rules out every integral third tangent intersection at $(-7, 8, -69)$.

## Reproduction and trust boundary

Run `lake -d .. env lean SecantOrbit.lean` and `gp -fq secant_orbit.gp`. Lean verifies the line identities, the exceptional sextic at $(0, 1, 1)$, the cubic norm identity, the split-prime determinant relation, and the fact that the tangent-direction cubic at any integer point has no repeated root. PARI/GP runs the Thue solves and finite enumerations.
