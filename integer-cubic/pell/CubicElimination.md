# Excluding the six cubic lifts through $(0,1,1)$

On the Pell conic $u^2 - 3v^2 = 1$, set

$$
L = 1 - 3t^2, \quad u = \frac{1 + 3t^2}{L}, \quad v = \frac{2t}{L}.
$$

Any polynomial of total degree at most 3 in $u$ and $v$ has the form $X(t)/L^3$ with $\deg X \le 6$. Write the three coordinates as $(X, Y, Z)/L^3$ with constant terms $(0, 1, 1)$ at the seed $t = 0$. The cubic surface equation becomes

$$
X^3 + ZY^2 + Z^2 L^3 = 2 L^9.
$$

The 18 nonconstant coefficients of $X, Y, Z$ must satisfy 18 equations.

No rational solution of this system with 7-integral coefficients and $\gcd(\bar X, \bar L) = 1$ modulo 7 passes through $(0, 1, 1)$. The coprimality condition means $\bar X$ keeps its poles at both roots of $L$ modulo 7. The proof combines exact finite-field checks, Hensel's lemma, and an integer resultant.

A general pole-order constraint also holds for every nonsplit Pell discriminant. If $x$ has pole order 3, then $y$ also has pole order 3, and $z$ and $z + y^2$ have pole orders 3 and 6 in some order: both orders are multiples of 3 summing to 9, and the larger order equals the pole order of their difference $y^2$, which is even. So any search where all three coordinates have degree at most 3 can take $z$ to have pole order 3 and $z + y^2$ to have pole order 6. See [PoleOne.lean](PoleOne.lean) for the Lean proof.

## A nine-variable system with the same six lifts

For a scalar $b$, define

$$
s = \frac{t + bt^2}{L}, \qquad r = \frac{1 + 2bt + 3t^2}{L}, \qquad r^2 = 1 + 4bs + 12s^2.
$$

Take cubics $C(s), J(s)$ and a quadratic $E(s)$ with $C(0) = 0$ and $J(0) = E(0) = 1$, and set $x = C(s)$, $z = J(s)$, $y = r E(s)$. The identity

$$
C^3 + J^2 + (1 + 4bs + 12s^2) E^2 J = 2
$$

gives 9 equations in the 9 unknowns ($b$, the 3 nonconstant coefficients of $C$, the 3 of $J$, and the 2 of $E$, in that column order for the Jacobian).

An exhaustive search over $\mathbb{F}_7$ finds 6 solutions to the full 18-variable system with $\gcd(\bar X, \bar L) = 1$. Every one of them comes from this 9-variable system, and $X'(0)$ tells the 6 solutions apart. The last two columns are used in the next section to normalize their cubic root fields.

| $X'(0)$ | $b$ | Reduced Jacobian determinant | $w$ | $a$ |
| --- | --- | --- | --- | --- |
| 1 | 5 | 5 | 1 | 0 |
| 2 | 5 | 5 | 4 | 0 |
| 3 | 2 | 2 | 2 | 0 |
| 4 | 5 | 5 | 2 | 0 |
| 5 | 2 | 2 | 4 | 0 |
| 6 | 2 | 2 | 1 | 0 |

For instance, the first row has $C = s + 4s^2 + 3s^3$, $J = 1 + 5s + 6s^3$, and $E = 1 + 5s^2$. Both the 9-variable and 18-variable Jacobians are invertible modulo 7 for all 6 rows. By multivariate Hensel lifting, each residue class has a unique $\mathbb{Z}_7$-lift in each system. Substituting the reduced lift into the full system produces a full lift in the same class, so uniqueness identifies the two. Every rational solution in these 6 classes must therefore have this 9-variable form over $\mathbb{Q}_7$. The enumeration and Jacobian checks are in [search_pell_mod.py](search_pell_mod.py) and [cubic_elimination_symmetry.py](cubic_elimination_symmetry.py).

For rational $X, Y, Z$, this representation actually holds over $\mathbb{Q}$. In every row, [cubic_elimination_symmetry.py](cubic_elimination_symmetry.py) checks that

$$
\gcd\big(C(s)/s, (J(s) - 1)/s\big) = 1 \pmod 7.
$$

Both leading coefficients are 7-adic units, so their resultant is nonzero in $\mathbb{Q}_7$. Since $b^2 \ne 3 \pmod 7$, the polynomials $t + bt^2$ and $L$ are also coprime. Clearing denominators shows that the monic gcd of $X(t)$ and $Z(t) - L^3$ is the monic associate of $t(1 + bt)$. Computing that monic gcd over $\mathbb{Q}$ gives the same polynomial, so $b \in \mathbb{Q}$. Because $s = t + O(t^2)$ and $r = 1 + O(t)$ at $t = 0$, matching Taylor coefficients recovers $C, J, E$ over $\mathbb{Q}$.

## Two rational parameters for the cubic divisor

At any root $\theta$ of $J$, the surface equation gives $C(\theta)^3 = 2$. Because $J$ is cubic and $T^3 - 2$ is irreducible, $J$ is irreducible and

$$
\mathbb{Q}(\theta) = \mathbb{Q}(C(\theta)) = \mathbb{Q}(\alpha), \qquad \alpha^3 = 2.
$$

Identify $C(\theta) = \alpha$ and write $\theta = c + i\alpha + j\alpha^2$. Since the leading coefficient of $J$ is a 7-adic unit, $\theta$ is integral at 7. The basis $1, \alpha, \alpha^2$ has discriminant $-108$, which is also a 7-adic unit, so $c, i, j$ are integral at 7. Solving $J(\theta) = 0$ and $C(\theta) = \alpha$ in $\mathbb{F}_7[\alpha]/(\alpha^3 - 2)$ gives $c = 0$ and $i \ne 0$ in all 6 rows. Changing variables to $s' = (s - c)/i$ moves the root to $\alpha + w\alpha^2$ and the seed to $a$, where $w = j/i$ and $a = -c/i$ have the residues listed in the table above.

To remove the cube-root symmetries, set $W = w^3$, $S = w s'$, and $B = wa$. Every row then satisfies $(W, B) \equiv (1, 0) \pmod 7$. Define

$$
P(S) = S^3 - 6WS - 2W - 4W^2, \quad G(S) = S - S^2 + 4W, \quad k = W(1 - 2W)^3,
$$

and put $A = P(B)$, $H = G(B)$. At $S = w(\alpha + w\alpha^2)$, we have $P(S) = 0$ and $G(S) = w(1 - 2W)\alpha$. Because $z$ is cubic and equals 1 at $S = B$, it must be $P(S)/A$. Similarly, $x - G(S)/(w(1 - 2W))$ is a multiple of $P$ of degree at most 3, and evaluating at $S = B$ gives

$$
z = \frac{P(S)}{A}, \qquad x = \frac{A G(S) - H P(S)}{w(1 - 2W)A}.
$$

All denominators are nonzero modulo 7. Set $Q(S) = (2k - G(S)^3)/P(S)$, which is a polynomial by the cube-root identity. Then $k A^2 y^2 = F(S)$, where

$$
F = A^3 Q + 3 A^2 H G^2 - 3 A H^2 G P + H^3 P^2 - A k P.
$$

Multiplying both sides by $P$ confirms this as an exact polynomial identity.

## The discriminant obstruction

In a rational lift, the 9-variable form and the invertible affine map from $s$ to $S$ force $F(S)$ to be a nonzero scalar times a quadratic times the square of a quadratic. It has degree 6 with leading coefficient $H^3 \ne 0$, and $\deg E = 2$ in all 6 rows. Therefore $F$ and $\partial_S F$ share a divisor of degree at least 2 (including when $E$ itself has a double root).

Let $R(W, B) = \operatorname{disc}_S(F)$. At any solution $(W, B)$, the common divisor of degree at least 2 gives the Sylvester matrix of $F$ and $\partial_S F$ corank at least 2, so its determinant and all its first cofactors vanish. Differentiating the determinant with respect to $B$ also gives zero. Since the leading coefficient of $F$ is nonzero here, the relation between resultant and discriminant gives

$$
R(W, B) = \partial_B R(W, B) = 0.
$$

Exact factorization over $\mathbb{Z}$ gives, up to a nonzero rational constant,

$$
R = W^4 H^6 A^6 (2W - 1)^8 \, \Delta(W, B), \qquad \deg_W \Delta = 28, \quad \deg_B \Delta = 42.
$$

Every factor in front of $\Delta$ is nonzero at any pair reducing to $(1, 0)$ modulo 7, so $\Delta(W, B) = \partial_B \Delta(W, B) = 0$. The leading coefficient of $\Delta$ in $B$ is the constant 4, which makes $W$ a root of $\operatorname{disc}_B(\Delta)$, an integer polynomial of degree 1148. Up to a nonzero constant, it factors as

$$
W^{195} (2W - 1)^{660} P_{37}(W) P_{62}(W)^2 P_{44}(W)^3,
$$

where the subscripts denote degrees. For $P_{37}$ and $P_{62}$, reduction modulo 5 keeps a nonzero leading coefficient and has no root. The same holds for $P_{44}$ modulo 13. A rational root in lowest terms would give a projective root in the corresponding finite field, which is impossible. That leaves only $W = 0$ and $W = 1/2$, whose residues modulo 7 are 0 and 4. Every branch requires $W \equiv 1 \pmod 7$, ruling out all 6 lifts. See [cubic_elimination.py](cubic_elimination.py) for the exact discriminant computation and [CubicEliminant.lean](CubicEliminant.lean) for the Lean rational-root certificate.

## The other seed $(-2,3,1)$

For the same Pell conic and full-pole condition, reduction modulo 7 also gives 6 candidate triples through $(-2, 3, 1)$, and every one fails to lift modulo 49.

Take integral representatives of each triple with exact constant terms $-2, 3, 1$, and form the 18 nonconstant coefficients of the residual

$$
T = X^3 + ZY^2 + Z^2 L^3 - 2 L^9.
$$

The constant term is zero and the remaining 18 coefficients are divisible by 7. Lifting modulo 49 requires a vector $v$ of 18 correction digits solving $Jv \equiv -T/7 \pmod 7$, where the columns of $J$ are $3X^2 t^j$, $2ZY t^j$, and $(Y^2 + 2ZL^3) t^j$ for $1 \le j \le 6$. On every branch, $J$ has rank 16 while the augmented matrix has rank 17. For each of the 6 systems, Lean verifies a left-kernel vector that annihilates every column of $J$ but pairs to a nonzero value with the right-hand side. This rules out all rational models through $(-2, 3, 1)$ with 7-integral coefficients and full poles modulo 7. See [cubic_elimination_symmetry.py](cubic_elimination_symmetry.py) for the lift checks and [CubicLiftObstruction.lean](CubicLiftObstruction.lean) for the Lean certificate.

## A uniform obstruction for reflection-symmetric cubics

The same two-parameter elimination rules out reflection-symmetric cubic models over $\mathbb{Q}$ for any Pell discriminant. Suppose a model through $(0, 1, 1)$ has a rational quotient coordinate $s$ such that

$$
x = C(s), \qquad z = J(s), \qquad y^2 = R(s) E(s)^2,
$$

where $C, J \in \mathbb{Q}[s]$ are cubic, $R, E \in \mathbb{Q}[s]$, $\deg R \le 2$, and the seed sits at a rational value of $s$. Then no such model can satisfy the surface equation identically. This covers every quadratic cover $r^2 = R(s)$ with $x, z$ cubic in $s$ and $y = rE(s)$, regardless of the square class of the leading coefficient of $R$ (the reflection sends $r \mapsto -r$). The modulo-7 argument above shows that all 6 branches for $D = 3$ would have this symmetry.

Since $J \mid 2 - C^3$, a root $\theta$ of $J$ generates $\mathbb{Q}(\sqrt[3]{2})$ as before. Because $C$ and $J$ both have degree 3, $(2 - C^3)/J - J$ has degree 6. It equals $R E^2$ with $\deg R \le 2$, so $\deg E \ge 2$, and its discriminant must satisfy the same Sylvester corank-2 vanishing condition.

Write $\alpha = \sqrt[3]{2}$ and $\theta = c + i\alpha + j\alpha^2$, where at least one of $i, j$ is nonzero.

If both $i$ and $j$ are nonzero, shift and scale $s$ so the root becomes $\alpha + w\alpha^2$ with $w = j/i \ne 0$. The parameters $(W, B)$ now work directly over $\mathbb{Q}$. Here $A = P(B) \ne 0$ because the rational seed cannot be a root of the irreducible cubic $J$, and $H = G(B) \ne 0$ because $H = 0$ would drop $\deg x$ to at most 2. Also $W \ne 0$ and $2W - 1 \ne 0$, since a rational cube $w^3$ cannot equal $1/2$ (its 2-adic valuation is divisible by 3). Every factor pulled out of the sextic discriminant is nonzero, so the projected discriminant leaves only $W = 0$ or $W = 1/2$, ruling out this case.

If only one of $i$ and $j$ is nonzero, normalize the root to $\alpha^e$ with $e = 1$ or $2$. Keep $s$ for the shifted variable and write $a$ for the rational seed value. Set

$$
P = s^3 - 2^e, \quad A = a^3 - 2^e, \quad H = s^e, \quad B = a^e.
$$

At the normalized root, $H/e = \alpha$, so interpolation gives

$$
z = \frac{P}{A}, \qquad x = \frac{AH - BP}{eA}.
$$

With $Q = (2e^3 - H^3)/P$, the sextic $e^3 A^2 y^2$ becomes

$$
F = A^3 Q + 3 A^2 B H^2 - 3 A B^2 H P + B^3 P^2 - e^3 A P.
$$

Exact factorization of $\operatorname{disc}_s F$ gives the factors below. For every nonlinear factor, reduction at the listed test prime keeps the same degree and has no root, ruling out rational roots.

| Normalized root | Factor vanishing at $a = 0$ | Other factor degrees (multiplicity, test prime) |
| --- | --- | --- |
| $\alpha$ | $a^6$ | $3\ (6, 7)$, $24\ (1, 5)$ |
| $\alpha^2$ | $a^{12}$ | $3\ (6, 7)$, $9\ (1, 5)$, $33\ (1, 5)$ |

The only possible rational root is $a = 0$, which gives $B = 0$ and $x = H/e$ of degree at most 2. This closes both exceptional normalizations and completes the uniform obstruction. See [cubic_elimination_symmetry.py](cubic_elimination_symmetry.py) for the exact factorizations and residue checks.

## Reproduce the computations

```sh
uv run --with python-flint==0.9.0 cubic_elimination_symmetry.py
uv run --with python-flint==0.9.0 cubic_elimination.py
lake -d .. build CubicEliminant CubicLiftObstruction
```

The first script enumerates both seeds and checks the Jacobians and exceptional normalizations. The second recomputes both integer discriminants, multiplies their factors back together, and checks the coefficients against the Lean input. Lean verifies that the final polynomial has only the two stated rational roots and excludes $W \equiv 1 \pmod 7$. Connecting a candidate substitution to a root of that polynomial relies on the lifting and descent steps written above.
