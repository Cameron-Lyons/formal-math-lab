# Cubic-field factors and local obstructions for quartic Pell models

Consider a quartic Pell model on $u^2 - 3v^2 = 1$ passing through $(0, 1, 1)$. With $L = 1 - 3t^2$, it is defined by polynomials $X, Y, Z \in \mathbb{Q}[t]$ satisfying

$$
X^3 + ZY^2 + Z^2 = 2 L^{12}, \qquad
\deg(X, Y, Z) \le (8, 6, 12), \qquad
(X, Y, Z)(0) = (0, 1, 1).
$$

Assume $\gcd(X, L) = 1$ over $\mathbb{Q}$. Geometrically, this map traces a rational curve of degree $12$ on the smooth projective cubic surface $S : x^3 + y^2 z + z^2 w = 2w^3$. Every smooth cubic surface contains **27 lines**, and how our curve intersects those $27$ lines gives rigid, height-free algebraic and local obstructions!

Using exact polynomial factorization and finite-field linear algebra in [quartic_local_geometry.py](quartic_local_geometry.py) (plus a Lean certificate at $p = 2$), this document establishes:

* **Cubic-field factorization:** Finding a degree-$12$ divisor $Z \mid 2L^{12} - X^3$ over $\mathbb{Q}$ reduces to finding two degree-$4$ polynomials $U, V$ over $\mathbb{Q}(\sqrt[3]{2})$.
* **27-line intersection law:** The $27$ lines split into two Galois orbits (size $3$ and size $24$), and every line pulls back to a divisor of degree exactly $4$ on the curve. At $p = 7$, the two smooth rank-$24$ quartic components where reduced $y$ has pole order $3$ both pass the line-intersection test; at $p = 5$, it eliminates $48$ of $157$ residue classes (and lifting mod $25$ eliminates another $24$).
* **Local obstructions at $p = 2$ and $p = 3$:** No $2$-integral $t$-chart keeping its poles ($\bar X(1) = 1$) exists ([QuarticBadTwo.lean](QuarticBadTwo.lean)); any $3$-integral $t$-chart must drop its degrees modulo $3$ to $\le (4, 3, 6)$; and any $2$-integral substitution directly in $(u, v)$ must take parity $(0, 1, 1)$ at every integer point of the Pell conic.

## A factorization over $\mathbb{Q}(\sqrt[3]{2})$

Set $\alpha = \sqrt[3]{2}$ and $K = \mathbb{Q}(\alpha)$, and let $\alpha_1, \alpha_2, \alpha_3$ be the three cube roots of $2$ in a splitting field. Factor the right-hand side of $Z(Z + Y^2) = 2L^{12} - X^3$ as

$$
Z(Z + Y^2) = \prod_{i=1}^3 (\alpha_i L^4 - X).
$$

* **Pairwise coprimality:** Any common root of $\alpha_i L^4 - X$ and $\alpha_j L^4 - X$ ($i \ne j$) would force $L = X = 0$, contradicting $\gcd(X, L) = 1$.
* **Exact degrees:** Since the leading coefficient of $X/L^4$ is rational, $2L^{12} - X^3$ cannot lose degree, so $\deg\bigl(Z(Z + Y^2)\bigr) = 24$, forcing $\deg Z = \deg(Z + Y^2) = 12$.

Now define $U_i = \gcd(Z, \alpha_i L^4 - X)$, scaled so that $U_i(0) = 1$. Because the three factors $\alpha_i L^4 - X$ are pairwise coprime, $Z = U_1 U_2 U_3$. The Galois group permutes $U_1, U_2, U_3$ transitively, so each $U_i$ has degree $4$. Setting $V_i = (\alpha_i L^4 - X)/U_i$ yields degree-$4$ polynomials with $V_i(0) = \alpha_i$.

Taking the pair $(U, V)$ indexed by $\alpha$, we obtain

$$
UV = \alpha L^4 - X, \qquad
N_{K/\mathbb{Q}}(U) = Z, \qquad
N_{K/\mathbb{Q}}(V) - N_{K/\mathbb{Q}}(U) = Y^2,
$$

where the norm multiplies the three coefficientwise conjugates. Conversely, multiplicativity of the norm immediately recovers $Z(Z + Y^2) = N(\alpha L^4 - X) = 2L^{12} - X^3$. Explicitly, writing $U = A + B\alpha + C\alpha^2$ gives

$$
N_{K/\mathbb{Q}}(U) = A^3 + 2B^3 + 4C^3 - 6ABC.
$$

This replaces searching for a degree-$12$ divisor of $2L^{12} - X^3$ over $\mathbb{Q}$ with finding two degree-$4$ polynomials over $K$.

## Intersections with the 27 lines

Consider the projective cubic surface $S : x^3 + y^2 z + z^2 w = 2w^3$. Let us classify all $27$ of its lines explicitly:

1. **Three horizontal lines ($z = 0$):** Setting $z = 0$ cuts out $x^3 = 2w^3$, giving the three lines $z = 0, x = \alpha_i w$. They form a single Galois orbit of size $3$.
2. **No lines in $w = 0$ or constant-$y$ planes:** The plane $w = 0$ cuts out $x^3 + y^2 z = 0$ (a cuspidal cubic, containing no lines), and in $w = 1$ every constant-$y$ fiber $(2z + y^2)^2 = y^4 + 8 - 4x^3$ is irreducible even over $\overline{\mathbb{Q}}$ (being a cuspidal cubic when $y^4 = -8$ and a smooth elliptic curve otherwise).
3. **Twenty-four sloped lines:** Every remaining line can therefore be written in $w = 1$ as $x = ay + b$, $z = cy + d$ with $a \ne 0$. Substituting into $x^3 + y^2 z + z^2 = 2$ and equating coefficients of $y^3, y^2, y^1, y^0$ gives

   $$
   c = -a^3, \qquad b = a^4 r, \qquad d = -a^6(3r + 1), \qquad
   3r^2 + 6r + 2 = 0, \qquad a^{12}(-26r - 11) = 6.
   $$

   Eliminating $r$ shows that the $24$ slopes $a$ are precisely the roots of

   $$
   a^{24} + 540a^{12} - 108 = 0,
   $$

   which is irreducible over $\mathbb{Q}$. Thus all $24$ sloped lines form a **single Galois orbit**.

### Why every one of the 27 lines pulls back to degree 4

Homogenizing $(XL^2, YL^3, Z, L^6)$ to degree $12$ gives a morphism $\mathbb{P}^1 \to S$. These four binary forms have no common zero: at any root of $L$, $\gcd(X, L) = 1$ and $X^3 + ZY^2 + Z^2 = 2L^{12}$ force $Z \ne 0$. Hence any plane section not containing the image pulls back to a divisor of degree $12$.

* By the cubic-field factorization above, each of the $3$ horizontal lines ($z = 0, x = \alpha_i w$) pulls back to $\deg U_i = 4$.
* By Galois conjugacy, all $24$ sloped lines share the same pullback degree $d$.
* Every sloped line meets a horizontal line where $z = 0$, and the plane spanned by those two intersecting lines cuts $S$ in those two lines plus a third line (counted with multiplicity). Our curve cannot lie inside this union of lines: if a nonconstant $\mathbb{Q}$-rational map landed in one line, it would have to land in all of its Galois conjugates too. Therefore the three pullback degrees sum to $12$: whether the third line is horizontal ($4 + 4 + d = 12$) or sloped ($4 + d + d = 12$), we obtain **$d = 4$**!

### The line-intersection test at $p = 5$

Now work at $p = 5$ and assume the chart coefficients are $5$-integral. Modulo $5$, $T^3 - 2$ factors as $(T - 3)(T^2 + 3T + 4)$, so the three horizontal lines split into two residue orbits of sizes $1$ and $2$.

**Why the degree-$4$ condition survives reduction even if $X$ loses poles:** Since $U_i(0) = 1$ and $Z = U_i (Z/U_i)$ is $5$-integral with constant term $1$, multiplicativity of the Gauss norm forces both $U_i$ and $Z/U_i$ to be $5$-integral. The same applies to $V_i$ via $\alpha_i L^4 - X = U_i V_i$. Homogenizing to degree-$12$ binary forms before reducing modulo $5$ therefore preserves a nonzero degree-$4$ common binary factor of the reductions of $Z$ and $X - \alpha_i L^4$ (counting factors at infinity).

In [quartic_local_geometry.py](quartic_local_geometry.py), enumerating all $157$ quartic residues modulo $5$ shows that $109$ pass the horizontal-line test:

* Out of $150$ full-pole residues, $104$ pass the line test; $24$ of those fail the first-lift equations modulo $25$, leaving $80$.
* Both residues where reduced $x$ has pole order $3$ fail the line test, leaving $5$ surviving residues of pole orders $0$, $1$, and $2$.

For each sloped residue line, its intersection degree is the degree of the homogeneous gcd of $X - aYL - bL^4$ and $Z - cYL^3 - dL^6$. Checking all $27$ lines leaves the exact same $109$ candidates.

## The primes 2 and 3 in the rational $t$-chart

### Prime $p = 2$: full-pole charts are impossible

At $p = 2$, $\bar L = 1 - 3t^2 \equiv (t + 1)^2 \pmod 2$, so keeping the poles in the $t$-chart means $\bar X(1) = 1$.

For each of the $128$ candidate numerators $X \in \mathbb{F}_2[t]$ (with $X(0) = 0, X(1) = 1, \deg X \le 8$), factoring $X^3$ in $\mathbb{F}_2[t]$ and testing all degree-bounded divisors $Z$ with $Z(0) = 1$ for $X^3/Z - Z$ to be a square of degree at most $12$ yields $7$ triples. Their mod-$4$ lifting matrices have rank $18$ (four triples) or rank $20$ (three triples), and in **every** case the augmented rank is one higher.

> **Theorem ([QuarticBadTwo.lean](QuarticBadTwo.lean)).** No quartic $t$-chart with $2$-integral coefficients and $\bar X(1) = 1$ can satisfy the cubic identity.

Lean verifies an explicit left-nullspace obstruction vector for all $7$ triples in [QuarticBadTwo.lean](QuarticBadTwo.lean). (Note why this does *not* yet rule out $2$-integral polynomials in $u, v$: any integral polynomial in $u, v$ automatically loses both poles modulo $2$ in the $t$-chart, because $L = 1 - 3t^2$, $1 + 3t^2$, and $2t$ all vanish modulo $2$ at $t = 1$.)

### Prime $p = 3$: forced degree drop modulo 3

At $p = 3$, $\bar L = 1$. Testing all $6{,}561$ numerators $X \in \mathbb{F}_3[t]$ yields $759$ triples modulo $3$, of which only $21$ have consistent lifting equations modulo $9$. All $21$ satisfy

$$
\deg \bar X \le 4, \qquad \deg \bar Y \le 3, \qquad \deg \bar Z \le 6.
$$

These degree drops are height-free necessary divisibility conditions for any $3$-integral rational $t$-chart. They also remain valid after any rescaling $t \mapsto 3^h t$ ($h \ge 0$) that produces $3$-integral coefficients, because $2(1 - 3^{2h+1} t^2)^{12} \equiv 2 \pmod 9$.

## Integral coefficients in the original Pell coordinates at 2

To test $2$-integral polynomials in $(u, v)$ directly — sidestepping the pole collapse at $t = 1$ modulo $2$ — change to the shifted generator $w = u - 1 - v$ in the Pell ring $\mathbb{Z}_2[u, v]/(u^2 - 3v^2 - 1)$. Using $u = w + 1 + v$ and $u^2 = 1 + 3v^2$ yields a relation whose right-hand side is **divisible by $2$**:

$$
w^2 = 2(v^2 - v) - 2(1 + v)w.
$$

Each coordinate of total degree at most $d$ ($d = 4, 3, 6$) writes uniquely as $P(v) + wQ(v)$ with $\deg P \le d$ and $\deg Q < d$. Because $w^2 \equiv 0 \pmod 2$, expanding $x^3 + y^2 z + z^2 = 2$ modulo $2$ decouples cleanly into base and $w$-components:

$$
P_x^3 + P_y^2 P_z + P_z^2 = 0, \qquad P_x^2 Q_x + P_y^2 Q_z = 0.
$$

* The first equation has $10$ solutions matching the seed $(0, 1, 1)$.
* The second equation expands those $10$ base triples into $1{,}040$ six-polynomial residues $(P_x, Q_x, P_y, Q_y, P_z, Q_z)$ modulo $2$.
* Lifting modulo $4$ using the exact formula for $w^2$ produces $24$ nonconstant coefficient equations, which are inconsistent for $1{,}008$ of the $1{,}040$ residues.
* All $32$ surviving residues satisfy

$$
P_x \equiv 0, \qquad P_y \equiv P_z \equiv 1, \qquad Q_z \equiv 0 \pmod 2.
$$

Because $w = u - 1 - v$ is always even at every integer point on $u^2 - 3v^2 = 1$ (since $u$ and $v$ have opposite parity, $u - 1 - v \equiv 0 \pmod 2$), **every $2$-integral quartic substitution in $(u, v)$ must take parity $(0, 1, 1)$ at every integer point on the Pell conic** — even when poles coalesce modulo $2$ in the $t$-chart.

## Reproduce the finite checks

```sh
uv run --with python-flint==0.9.0 quartic_local_geometry.py --all-lines
```
