# Chords and tangents through the eight small points

Write $S$ for the eight points $(0,\pm1,1)$, $(0,\pm1,-2)$,
$(-7,\pm8,5)$, and $(-7,\pm8,-69)$ on $z^2+y^2z+x^3=2$.
Starting at $(0,1,1)$, the vertical chord reaches $(0,1,-2)$.
The line $(0,1,-2)+t(-1,1,1)$ reaches $(-7,8,5)$ at $t=7$.
Vertical chords send $z$ to $-y^2-z$, and chords parallel to the
$y$-axis send $y$ to $-y$. These steps reach all eight points. Conversely,
every integral third intersection obtained from these points by a chord
between two of them, a line to a rational point at infinity, or a tangent
at one of them also belongs to $S$. This computes the orbit when each
successive affine point must be integral.

| Affine point | Non-axis lines to infinity giving a second integer point | Tangent lines giving a second integer point |
| --- | ---: | ---: |
| $(0,1,1)$ | 0 | 0 |
| $(0,1,-2)$ | 1 | 0 |
| $(-7,8,5)$ | 1 | 0 |
| $(-7,8,-69)$ | 0 | 0 |

## Exhausting the line directions

For an integral point $P=(x,y,z)$ and a primitive integer direction
$D=(i,j,k)$, the cubic restricted to $P+tD$, after subtracting 2,
is $t(L+tQ+t^2C)$, where

$$
L=3x^2i+2yzj+(y^2+2z)k,\quad
Q=3xi^2+zj^2+2yjk+k^2,\quad C=i^3+j^2k.
$$

Any integer point on this line corresponds to an integer $t$, by
Bézout's identity for the components of $D$. Two kinds of lines
therefore give divisibility conditions.

- A chord through a rational point at infinity has $C=0$. The directions
  are $(-n^2m,n^3,m^3)$ for coprime $m,n$, up to sign. Indeed, when
  $j\ne0$, the ratio $m/n=-i/j$ determines $k/j=(m/n)^3$.
  The case $j=0$ is the vertical axis. A second point requires $Q\mid L$
  when $Q\ne0$.
- A tangent line at $P$ has $L=0$. Write its direction in a basis of
  the integer kernel of $L$, with coprime coordinates $m,n$. The
  third intersection has $t=-Q/C$ when $C\ne0$, so $C\mid Q$.

For the first type, the script forms the binary sextic $F=Q$ and
cubic $G=L$. For the second it takes the cubic $F=C$ and quadratic
$G=Q$. The exceptional first sextic at $(0,1,1)$ is handled by the
Lean theorem `seed_secant`, which forces $t n^2m=0$. The other
denominator forms have full degree in $m$ and are irreducible over the
rationals, so none vanishes at a primitive integer pair.

If $F(m,n)\mid G(m,n)$, every prime power dividing $F(m,n)$
divides a resultant. For a prime not dividing $n$, evaluate the
Bézout identity for $F(X,1)$ and $G(X,1)$ at $m/n$ modulo that
prime power. For a prime dividing $n$, use $F(1,X)$ and $G(1,X)$
at $n/m$. Thus $|F(m,n)|$ divides the least common multiple of
the absolute resultants. In the first six enumerations, for each surviving
signed divisor $d$, PARI solves $F(m,n)=d$ with `thueinit(F(X,1),1)` and `thue`. The flag
requests unconditional certification. The remaining tests on each
solution use exact arithmetic. [PARI documentation](https://pari.math.u-bordeaux.fr/dochtml/html/Polynomials_and_power_series.html#thue)

The change $y\mapsto-y$ preserves lines, so it suffices to check four
positive-$y$ representatives. For chords between two distinct members
of $S$, put $P'=P+hD$, with $D$ primitive. When $C\ne0$,
the product of the two roots of $L+tQ+t^2C$ gives the third
intersection parameter $t=L/(hC)$. The script checks all 28 pairs.

## The final tangent cubic

At $(-7,8,-69)$ the chosen integral tangent basis gives

$$
f(X)=F(X,1)=-213X^3+39450X^2-2430429X+49836032.
$$

Its resultant bound factors as $3^4\cdot23\cdot83\cdot347\cdot661090691$.
Reversing a direction changes the sign of $F$. Among the positive
divisors, 27 survive the primitive-pair and divisibility conditions
modulo 9. Let $a=-213$ and let $\theta$ be a root of $a^2 f(X/a)$.
Then $a m-\theta n$ is integral and has norm $a^2 F(m,n)$. PARI
certifies the cubic field with `bnfcertify` and returns all representatives
of the required norms modulo positive-norm units with `bnfisintnorm`.
There are 110 representatives across the 27 right-hand sides. The field
has unit rank one and torsion $\{\pm1\}$. [PARI number field documentation](https://pari.math.u-bordeaux.fr/dochtml/html/General_number_fields.html#bnfisintnorm)

Write $\beta$ for a norm representative and $u$ for a fundamental unit.
If $\pm\beta u^k=a m-\theta n$, its values at the three reductions
modulo a split prime $q$ must be a linear combination of the vectors
$(1,1,1)$ and $(\theta_1,\theta_2,\theta_3)$. The determinant test is

$$
(\theta_2-\theta_3)\beta_1 u_1^k
+(\theta_3-\theta_1)\beta_2 u_2^k
+(\theta_1-\theta_2)\beta_3 u_3^k=0\pmod q .
$$

The code checks all $k$ modulo $q-1$. For every representative it finds
a split prime $q\le2000$ where every exponent fails. It only uses primes
where all compact factors can be reduced and inverted. This excludes
every possible integral third tangent intersection at $(-7,8,-69)$.

Run `lake -d .. env lean SecantOrbit.lean` and `gp -fq secant_orbit.gp`.
Lean verifies the line identities, the exceptional sextic argument, the
cubic norm identity, and the linear relation at split primes. It also
proves that the tangent-direction cubic at any integer point has no
repeated root. PARI performs the finite enumerations.
