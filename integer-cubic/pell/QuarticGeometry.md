# Cubic-field factors and local obstructions for quartic Pell models

Consider a quartic model through $(0, 1, 1)$ on $u^2 - 3v^2 = 1$. With $L = 1 - 3t^2$, it satisfies

$$
X^3 + ZY^2 + Z^2 = 2 L^{12}, \qquad
\deg(X, Y, Z) \le (8, 6, 12), \qquad (X, Y, Z)(0) = (0, 1, 1).
$$

Assume $\gcd(X, L) = 1$ over $\mathbb{Q}$. Modulo 7, the two smooth rank-24 quartic components where reduced $y$ has pole order 3 both pass the line-intersection test. At other primes, the tests below rule out entire residue classes with no height bound, using exact polynomial factorization and finite-field linear algebra in [quartic_local_geometry.py](quartic_local_geometry.py).

## A factorization over the cubic field

Set $\alpha = \sqrt[3]{2}$ and $K = \mathbb{Q}(\alpha)$. Over a splitting field, the three polynomials $\alpha_i L^4 - X$ (with $\alpha_i^3 = 2$) are pairwise coprime, since a common root would force $L = X = 0$. Their product is $Z(Z + Y^2)$. Both $Z$ and $Z + Y^2$ have degree 12, because their product has degree 24 (the leading coefficient of $X/L^4$ is rational, so $2L^{12} - X^3$ cannot lose degree).

Define $U_i = \gcd(Z, \alpha_i L^4 - X)$, scaled so that $U_i(0) = 1$. Since the three larger factors are pairwise coprime, the product of the $U_i$ is $Z$. The Galois group permutes them transitively, so each $U_i$ has degree 4. Set $V_i = (\alpha_i L^4 - X)/U_i$; each $V_i$ also has degree 4 and constant term $\alpha_i$. Taking the pair indexed by $\alpha$ gives

$$
UV = \alpha L^4 - X, \qquad N_{K/\mathbb{Q}}(U) = Z, \qquad
N_{K/\mathbb{Q}}(V) - N_{K/\mathbb{Q}}(U) = Y^2,
$$

where the norm multiplies the three coefficientwise conjugates. Conversely, multiplicativity of the norm recovers the surface equation from these identities. Writing $U = A + B\alpha + C\alpha^2$ gives $N(U) = A^3 + 2B^3 + 4C^3 - 6ABC$. This replaces choosing a degree-12 divisor of $2L^{12} - X^3$ by finding two degree-4 polynomials over $K$.

## Intersections with the 27 lines

The projective cubic surface is $x^3 + y^2 z + z^2 w = 2w^3$. Three horizontal lines $z = 0$, $x = \alpha_i w$ form the plane section $z = 0$. No line lies in the cuspidal plane $w = 0$, and at constant $y$ the affine fiber $(2z + y^2)^2 = y^4 + 8 - 4x^3$ is irreducible even over $\overline{\mathbb{Q}}$. Every other line can therefore be written in $w = 1$ as $x = ay + b$, $z = cy + d$ with $a \ne 0$. Equating coefficients gives

$$
c = -a^3, \qquad b = a^4 r, \qquad d = -a^6(3r + 1), \qquad
3r^2 + 6r + 2 = 0, \qquad a^{12}(-26r - 11) = 6.
$$

The 24 slopes are the roots of $a^{24} + 540a^{12} - 108$, which is irreducible over $\mathbb{Q}$, so all 24 sloped lines form a single Galois orbit.

Our rational quartic map into the projective surface is given by the degree-12 homogenizations of $(XL^2, YL^3, Z, L^6)$. These four forms have no common zero: at a root of $L$, $\gcd(X, L) = 1$ and the cubic identity force $Z \ne 0$. Any plane section that does not contain the image therefore pulls back to a divisor of degree 12.

By the factorization above, each horizontal line pulls back to degree 4. By Galois conjugacy, all 24 sloped lines have the same pullback degree $d$. Every sloped line meets a horizontal line where $z = 0$, and the plane through them cuts the surface in those two lines plus a third line (counted with multiplicity). The curve cannot lie inside this union of lines: if a nonconstant rational map landed in one line, it would have to land in all of its Galois conjugates too. The three pullback degrees must sum to 12, forcing $d = 4$ whether the third line is horizontal or sloped.

Now work at $p = 5$ and assume the chart coefficients are 5-integral. The horizontal lines split into two residue orbits of sizes 1 and 2, and both must keep pullback degree at least 4 modulo 5, even if $X$ loses poles on reduction. Why? Because $U_i(0) = 1$ and $Z = U_i (Z/U_i)$ is 5-integral with constant term 1, multiplicativity of the Gauss norm forces both normalized factors to be 5-integral. The same holds for $V_i$ via $\alpha_i L^4 - X = U_i V_i$. Homogenizing before reduction therefore leaves a nonzero degree-4 common binary factor of the reductions of $Z$ and $X - \alpha_i L^4$ (including factors at infinity).

In [quartic_local_geometry.py](quartic_local_geometry.py), enumerating all 157 quartic residues modulo 5 shows that 109 pass the horizontal-line test:

* Out of 150 full-pole residues, 104 pass the line test; 24 of those fail the first-lift equations modulo 25, leaving 80.
* Both residues where reduced $x$ has pole order 3 fail the line test, leaving 5 surviving residues of pole orders 0, 1, and 2.

For each sloped residue line, its intersection degree is the degree of the homogeneous gcd of $X - aYL - bL^4$ and $Z - cYL^3 - dL^6$. Checking all 27 lines leaves the exact same 109 candidates.

## The primes 2 and 3 in the rational chart

At $p = 2$, we have $\bar L = (t + 1)^2$, so keeping the poles in the $t$-chart requires $\bar X(1) = 1$. For each of the 128 candidate numerators $X$, factoring $X^3$ in $\mathbb{F}_2[t]$ and testing all degree-bounded divisors $Z$ with $Z(0) = 1$ for $X^3/Z - Z$ to be a square of degree at most 12 yields 7 triples. Their mod-4 lifting matrices have rank 18 (four triples) or rank 20 (three triples), and in every case the augmented rank is one higher. **No chart with 2-integral coefficients and $\bar X(1) = 1$ can satisfy the identity.** Lean checks an explicit left-nullspace obstruction for all 7 triples in [QuarticBadTwo.lean](QuarticBadTwo.lean). Note that any integral polynomial in $u, v$ loses both poles modulo 2 in the $t$-chart, because $L$, $1 + 3t^2$, and $2t$ all vanish modulo 2 at $t = 1$.

At $p = 3$, $\bar L = 1$. Testing all 6,561 numerators $X$ gives 759 triples modulo 3, of which 21 have consistent lifting equations modulo 9. All 21 satisfy $\deg \bar X \le 4$, $\deg \bar Y \le 3$, and $\deg \bar Z \le 6$. These degree drops are necessary divisibility conditions for any 3-integral rational chart of any height. They also apply after any rescaling $t \mapsto 3^h t$ ($h \ge 0$) that produces 3-integral coefficients, because $2(1 - 3^{2h+1} t^2)^{12} \equiv 2 \pmod 9$.

## Integral coefficients in the original Pell coordinates at 2

When the coefficients in $u$ and $v$ are 2-integral, we can test directly in the Pell ring without losing poles. Set $w = u - 1 - v$, which satisfies

$$
w^2 = 2(v^2 - v) - 2(1 + v)w.
$$

Each coordinate of degree at most $d$ ($d = 4, 3, 6$) writes uniquely as $P(v) + wQ(v)$ with $\deg P \le d$ and $\deg Q < d$. Modulo 2, the base and $w$-components of the cubic identity are

$$
P_x^3 + P_y^2 P_z + P_z^2 = 0, \qquad P_x^2 Q_x + P_y^2 Q_z = 0.
$$

The first equation has 10 solutions matching the seed, and the second expands them to 1,040 six-polynomial residues. Multiplying $P + wQ$ modulo 4 using the relation for $w^2$ gives 24 nonconstant coefficient equations, which are inconsistent for 1,008 of the 1,040 residues. All 32 survivors satisfy $P_x \equiv 0$, $P_y \equiv P_z \equiv 1$, and $Q_z \equiv 0 \pmod 2$. Therefore every 2-integral quartic substitution in $(u, v)$ takes parity $(0, 1, 1)$ at every integer point on the Pell conic (even when poles coalesce modulo 2 in the $t$-chart).

To reproduce all finite checks, run:

```sh
uv run --with python-flint==0.9.0 quartic_local_geometry.py --all-lines
```
