# Excluding the six cubic lifts through $(0,1,1)$

On the Pell conic $u^2 - 3v^2 = 1$, parametrize points rationally via $t$ by setting

$$
L = 1 - 3t^2, \qquad u = \frac{1 + 3t^2}{L}, \qquad v = \frac{2t}{L}.
$$

Any polynomial of total degree at most $3$ in $u$ and $v$ takes the form $X(t)/L^3$ with $\deg X \le 6$. Writing $(x, y, z) = (X, Y, Z)/L^3$ with constant terms $(0, 1, 1)$ at the seed $t = 0$, the cubic surface equation $x^3 + y^2 z + z^2 = 2$ becomes

$$
X^3 + ZY^2 + Z^2 L^3 = 2 L^9.
$$

Matching powers of $t$ from $t^1$ to $t^{18}$ gives $18$ equations in the $18$ nonconstant coefficients of $X, Y, Z$.

This document proves three obstructions by combining finite-field checks, Hensel's lemma, and exact integer resultants:

1. **Seed $(0, 1, 1)$ on $u^2 - 3v^2 = 1$:** No rational solution of the system above with $7$-integral coefficients and $\gcd(\bar X, \bar L) = 1$ modulo $7$ exists (the coprimality condition means $\bar X$ keeps its poles at both roots of $L$ modulo $7$).
2. **Seed $(-2, 3, 1)$ on $u^2 - 3v^2 = 1$:** Under the same $7$-integral full-pole assumptions, all $6$ candidate mod-$7$ triples fail to lift even to modulus $49$.
3. **Uniform reflection-symmetric obstruction (any Pell discriminant):** Over $\mathbb{Q}$, no cubic model through $(0, 1, 1)$ of the reflection-symmetric form $x = C(s)$, $z = J(s)$, $y^2 = R(s)E(s)^2$ ($\deg C = \deg J = 3$, $\deg R \le 2$) exists at all.

## Proof roadmap and pole-order setup

Why can we assume $x, y, z$ all share the denominator $L^3$? A general pole-order constraint holds for **every** nonsplit Pell discriminant: if $x$ has pole order $3$, then $y$ also has pole order $3$, and $z$ and $z + y^2$ have pole orders $3$ and $6$ in some order. Indeed, both orders must be multiples of $3$ summing to $9$, and the larger order equals the pole order of their difference $y^2$, which is even. Hence any search where all three coordinates have degree at most $3$ can take $z$ to have pole order $3$ and $z + y^2$ to have pole order $6$. See [PoleOne.lean](PoleOne.lean) for the Lean proof.

To eliminate the $18$-variable system through $(0, 1, 1)$, we compress the problem in three sharp drops in dimension:

$$
18 \text{ variables} \;\xrightarrow{\text{Hensel rigidity at } 7}\; 9 \text{ variables} \;\xrightarrow{\mathbb{Q}(\sqrt[3]{2}) \text{ root}}\; 2 \text{ variables } (W, B) \;\xrightarrow{\text{Sylvester corank } 2}\; 1 \text{ variable } W.
$$

1. **18 $\to$ 9 variables:** Modulo $7$, all $6$ full-pole solutions unexpectedly exhibit an extra reflection symmetry, fitting a $9$-variable system. Both Jacobians are invertible mod $7$, so Hensel uniqueness forces every $\mathbb{Z}_7$-lift to keep that symmetry, and a gcd descent transfers the representation to $\mathbb{Q}$.
2. **9 $\to$ 2 variables:** At a root $\theta$ of the cubic $z = J(s)$, $x(\theta)^3 = 2$, so $\theta \in \mathbb{Q}(\sqrt[3]{2})$. Expressing $\theta$ in the basis $1, \alpha, \alpha^2$ ($\alpha = \sqrt[3]{2}$) and modding out cube-root symmetries parametrizes the whole family by two rational numbers $(W, B)$.
3. **2 $\to$ 1 variable:** Because $y^2$ carries a squared quadratic factor $E^2$, the resulting sextic $F(S)$ and its derivative $\partial_S F$ share a divisor of degree at least $2$. That forces both the discriminant $R(W, B)$ and its derivative $\partial_B R(W, B)$ to vanish, pinning $W$ to a root of a single integer polynomial of degree $1{,}148$ whose only rational roots are $0$ and $1/2$ — contradicting $W \equiv 1 \pmod 7$.

## Step 1: A nine-variable system with the same six lifts

For a scalar $b$, define two rational functions on the Pell conic:

$$
s = \frac{t + bt^2}{L}, \qquad r = \frac{1 + 2bt + 3t^2}{L}, \qquad r^2 = 1 + 4bs + 12s^2.
$$

Take cubics $C(s), J(s)$ and a quadratic $E(s)$ with $C(0) = 0$ and $J(0) = E(0) = 1$, and set $x = C(s)$, $z = J(s)$, $y = r E(s)$. The surface equation becomes

$$
C^3 + J^2 + (1 + 4bs + 12s^2) E^2 J = 2,
$$

yielding $9$ polynomial coefficient equations in $9$ unknowns ($b$, the $3$ nonconstant coefficients of $C$, the $3$ of $J$, and the $2$ of $E$, in that column order for the Jacobian).

An exhaustive search over $\mathbb{F}_7$ finds exactly $6$ solutions to the full $18$-variable system with $\gcd(\bar X, \bar L) = 1$. Every one of them arises from this $9$-variable system, and $X'(0)$ separates all $6$ solutions. (The last two columns $w, a$ are used in Step 2 to normalize their cubic root fields.)

| $X'(0)$ | $b$ | Reduced Jacobian determinant | $w$ | $a$ |
| --- | --- | --- | --- | --- |
| 1 | 5 | 5 | 1 | 0 |
| 2 | 5 | 5 | 4 | 0 |
| 3 | 2 | 2 | 2 | 0 |
| 4 | 5 | 5 | 2 | 0 |
| 5 | 2 | 2 | 4 | 0 |
| 6 | 2 | 2 | 1 | 0 |

For instance, the first row has $C = s + 4s^2 + 3s^3$, $J = 1 + 5s + 6s^3$, and $E = 1 + 5s^2$.

### Lifting uniqueness and descent to $\mathbb{Q}$

Both the $9$-variable and $18$-variable Jacobians are invertible modulo $7$ in all $6$ rows. By multivariate Hensel lifting, each residue class has a unique $\mathbb{Z}_7$-lift in each system. Substituting the $9$-variable lift into the $18$-variable system produces an $18$-variable lift in the same residue class, so uniqueness forces the two to coincide. Every rational solution in these $6$ classes must therefore have this $9$-variable form over $\mathbb{Q}_7$. (The enumeration and Jacobian checks live in [search_pell_mod.py](search_pell_mod.py) and [cubic_elimination_symmetry.py](cubic_elimination_symmetry.py).)

If $X, Y, Z$ have rational coefficients, this $9$-variable form actually holds over $\mathbb{Q}$:

1. In every row, [cubic_elimination_symmetry.py](cubic_elimination_symmetry.py) verifies that

   $$
   \gcd\big(C(s)/s, (J(s) - 1)/s\big) = 1 \pmod 7.
   $$

2. Both leading coefficients are $7$-adic units, so their resultant is nonzero in $\mathbb{Q}_7$. Since $b^2 \not\equiv 3 \pmod 7$, the polynomials $t + bt^2$ and $L = 1 - 3t^2$ are also coprime.
3. Clearing denominators shows that the monic gcd of $X(t)$ and $Z(t) - L^3$ is the monic associate of $t(1 + bt)$. Computing that monic gcd over $\mathbb{Q}$ yields the exact same polynomial, forcing $b \in \mathbb{Q}$.
4. Because $s = t + O(t^2)$ and $r = 1 + O(t)$ at $t = 0$, matching Taylor coefficients at $t = 0$ recovers $C, J, E$ over $\mathbb{Q}$.

## Step 2: Two rational parameters for the cubic divisor

At any root $\theta$ of the cubic $J(s)$, the surface equation gives $C(\theta)^3 = 2$. Because $J$ is cubic and $T^3 - 2$ is irreducible over $\mathbb{Q}$, $J$ must be irreducible and

$$
\mathbb{Q}(\theta) = \mathbb{Q}(C(\theta)) = \mathbb{Q}(\alpha), \qquad \alpha^3 = 2.
$$

Identify $C(\theta) = \alpha$ and expand $\theta = c + i\alpha + j\alpha^2$ in the power basis of $\mathbb{Q}(\alpha)$. Since the leading coefficient of $J$ is a $7$-adic unit, $\theta$ is integral at $7$. The basis $1, \alpha, \alpha^2$ has discriminant $-108$, which is also a $7$-adic unit, so $c, i, j$ are all integral at $7$. Solving $J(\theta) = 0$ and $C(\theta) = \alpha$ in $\mathbb{F}_7[\alpha]/(\alpha^3 - 2)$ yields $c \equiv 0$ and $i \not\equiv 0 \pmod 7$ in all $6$ rows.

Change variables to $s' = (s - c)/i$. This moves the root $\theta$ to $\alpha + w\alpha^2$ and moves the seed $s = 0$ to $a$, where $w = j/i$ and $a = -c/i$ have the mod-$7$ residues recorded in the table above.

To quotient out cube-root symmetries, set

$$
W = w^3, \qquad S = w s', \qquad B = wa.
$$

In every row, this normalizes the residue to $(W, B) \equiv (1, 0) \pmod 7$. Now define the polynomials and constants

$$
P(S) = S^3 - 6WS - 2W - 4W^2, \qquad G(S) = S - S^2 + 4W, \qquad k = W(1 - 2W)^3,
$$

and put $A = P(B)$ and $H = G(B)$.

### Interpolating $z$, $x$, and $y^2$

At the root $S = w(\alpha + w\alpha^2)$, direct expansion using $\alpha^3 = 2$ and $w^3 = W$ shows that $P(S) = 0$ and $G(S) = w(1 - 2W)\alpha$.

* Because $z$ is cubic, vanishes at $S = w(\alpha + w\alpha^2)$, and equals $1$ at the seed $S = B$, it must be $z = P(S)/A$.
* Similarly, $x - G(S)/(w(1 - 2W))$ has degree at most $3$ and vanishes at the three conjugates of $S$, so it is a scalar multiple of $P(S)$; evaluating at $S = B$ (where $x = 0$) determines that scalar:

$$
z = \frac{P(S)}{A}, \qquad x = \frac{A G(S) - H P(S)}{w(1 - 2W)A}.
$$

All denominators are nonzero modulo $7$. Set $Q(S) = (2k - G(S)^3)/P(S)$, which is a polynomial because $G(S)^3 = 2k$ at the roots of $P$. Clearing denominators in $y^2 = (2 - x^3)/z - z$ yields $k A^2 y^2 = F(S)$, where $F(S)$ is the degree-6 polynomial

$$
F = A^3 Q + 3 A^2 H G^2 - 3 A H^2 G P + H^3 P^2 - A k P.
$$

Multiplying both sides by $P$ confirms this as an exact polynomial identity.

## Step 3: The discriminant obstruction

In any rational lift, the $9$-variable form $y^2 = (1 + 4bs + 12s^2)E(s)^2$ and the invertible affine map $s \mapsto S$ force $F(S)$ to be a nonzero scalar times a quadratic times the **square of a quadratic** (since $\deg E = 2$ in all $6$ rows). Moreover, $\deg F = 6$ with leading coefficient $H^3 \ne 0$.

Consequently, $F$ and $\partial_S F$ share a common divisor of degree at least $2$ (even if $E$ itself happens to have a double root).

### Why both $R$ and $\partial_B R$ vanish

Let $R(W, B) = \operatorname{disc}_S(F)$. At any solution $(W, B)$:

1. Because $\deg\gcd(F, \partial_S F) \ge 2$, the Sylvester matrix of $F$ and $\partial_S F$ has **corank at least $2$**.
2. Therefore not only its determinant vanishes, but **all of its first cofactors** vanish as well.
3. By Jacobi's formula for the derivative of a determinant, differentiating $\det(\mathrm{Syl}(F, \partial_S F))$ with respect to $B$ is a linear combination of first cofactors, so it vanishes too.
4. Since the leading coefficient of $F$ is nonzero, the standard proportionality between the Sylvester resultant and $\operatorname{disc}_S(F)$ gives

$$
R(W, B) = \partial_B R(W, B) = 0.
$$

### Exact factorization and rational-root elimination

Exact factorization over $\mathbb{Z}$ gives, up to a nonzero rational constant,

$$
R = W^4 H^6 A^6 (2W - 1)^8 \, \Delta(W, B), \qquad \deg_W \Delta = 28, \quad \deg_B \Delta = 42.
$$

Every prefactor in front of $\Delta$ is nonzero at any pair reducing to $(1, 0) \pmod 7$, so $\Delta(W, B) = \partial_B \Delta(W, B) = 0$. Because the leading coefficient of $\Delta$ in $B$ is the constant $4$, $W$ must be a root of $\operatorname{disc}_B(\Delta)$, an integer polynomial of degree $1{,}148$. Up to a nonzero constant, it factors as

$$
W^{195} (2W - 1)^{660} P_{37}(W) P_{62}(W)^2 P_{44}(W)^3,
$$

where the subscripts denote degrees:

* For $P_{37}$ and $P_{62}$, reduction modulo $5$ keeps a nonzero leading coefficient and has no root in $\mathbb{F}_5$.
* For $P_{44}$, reduction modulo $13$ keeps a nonzero leading coefficient and has no root in $\mathbb{F}_{13}$.

A rational root in lowest terms would give a projective root in the corresponding finite field, which is impossible. That leaves only $W = 0$ and $W = 1/2$, whose residues modulo $7$ are $0$ and $4$. Since every branch requires $W \equiv 1 \pmod 7$, **all $6$ lifts are ruled out**. See [cubic_elimination.py](cubic_elimination.py) for the exact discriminant computation and [CubicEliminant.lean](CubicEliminant.lean) for the Lean rational-root certificate.

## The other seed $(-2,3,1)$

For the same Pell conic $u^2 - 3v^2 = 1$ and the same $7$-integral full-pole condition, reduction modulo $7$ again yields $6$ candidate triples through $(-2, 3, 1)$ — and here the obstruction happens immediately at the very first lift modulo $49$.

Take integral representatives of each triple with exact constant terms $-2, 3, 1$, and form the $18$ nonconstant coefficients of the residual

$$
T = X^3 + ZY^2 + Z^2 L^3 - 2 L^9.
$$

The constant term is zero and the remaining $18$ coefficients are divisible by $7$. Lifting modulo $49$ requires a vector $v \in \mathbb{F}_7^{18}$ of first-order correction digits solving

$$
Jv \equiv -\frac{T}{7} \pmod 7,
$$

where the columns of $J$ are $3X^2 t^j$, $2ZY t^j$, and $(Y^2 + 2ZL^3) t^j$ for $1 \le j \le 6$.

On every branch, $J$ has rank $16$ while the augmented matrix $[J \mid -T/7]$ has rank $17$. For each of the $6$ systems, Lean verifies an explicit left-kernel vector that annihilates every column of $J$ yet pairs to a nonzero value with the right-hand side. This rules out all rational models through $(-2, 3, 1)$ with $7$-integral coefficients and full poles modulo $7$. See [cubic_elimination_symmetry.py](cubic_elimination_symmetry.py) for the lift checks and [CubicLiftObstruction.lean](CubicLiftObstruction.lean) for the Lean certificate.

## A uniform obstruction for reflection-symmetric cubics

The same two-parameter elimination rules out reflection-symmetric cubic models over $\mathbb{Q}$ for **any** Pell discriminant, with no $7$-adic hypothesis at all.

> **Theorem.** Suppose a model through $(0, 1, 1)$ has a rational quotient coordinate $s$ such that
>
> $$
> x = C(s), \qquad z = J(s), \qquad y^2 = R(s) E(s)^2,
> $$
>
> where $C, J \in \mathbb{Q}[s]$ are cubic, $R, E \in \mathbb{Q}[s]$, $\deg R \le 2$, and the seed $(0, 1, 1)$ sits at a rational value of $s$. Then no such model can satisfy the surface equation identically.

This covers every quadratic cover $r^2 = R(s)$ with $x, z$ cubic in $s$ and $y = rE(s)$, regardless of the square class of the leading coefficient of $R$ (the reflection sends $r \mapsto -r$). As shown in Step 1 above, all $6$ branches for $D = 3$ would automatically possess this symmetry.

### Proof over $\mathbb{Q}$

Since $J \mid 2 - C^3$, a root $\theta$ of $J$ generates $\mathbb{Q}(\alpha)$ ($\alpha = \sqrt[3]{2}$) as before. Because $C$ and $J$ both have degree $3$, the polynomial $(2 - C^3)/J - J$ has degree $6$. It equals $R E^2$ with $\deg R \le 2$, forcing $\deg E \ge 2$, so its discriminant must satisfy the same Sylvester corank-$2$ vanishing condition.

Write $\theta = c + i\alpha + j\alpha^2$, where at least one of $i, j \in \mathbb{Q}$ is nonzero.

#### Case 1: Both $i$ and $j$ are nonzero

Shift and scale $s$ so the root becomes $\alpha + w\alpha^2$ with $w = j/i \ne 0$. The parameters $(W, B)$ from Step 2 now work directly over $\mathbb{Q}$, and every prefactor in $R = W^4 H^6 A^6 (2W - 1)^8 \Delta(W, B)$ is forced to be nonzero:

* $A = P(B) \ne 0$, because the rational seed cannot be a root of the irreducible cubic $J$;
* $H = G(B) \ne 0$, because $H = 0$ would drop $\deg x$ to at most $2$;
* $W = w^3 \ne 0$ since $w \ne 0$;
* $2W - 1 \ne 0$, because a rational cube $w^3$ cannot equal $1/2$ (its $2$-adic valuation is divisible by $3$).

Hence $\Delta(W, B) = \partial_B \Delta(W, B) = 0$, and the degree-$1{,}148$ projected discriminant leaves only $W = 0$ or $W = 1/2$, both already ruled out.

#### Case 2: Only one of $i$ and $j$ is nonzero

Normalize the root to $\alpha^e$ with $e = 1$ or $2$. Keep $s$ for the shifted variable, write $a \in \mathbb{Q}$ for the rational seed value, and set

$$
P = s^3 - 2^e, \qquad A = a^3 - 2^e, \qquad H = s^e, \qquad B = a^e.
$$

At the normalized root, $H/e = \alpha$, so interpolation gives

$$
z = \frac{P}{A}, \qquad x = \frac{AH - BP}{eA}.
$$

With $Q = (2e^3 - H^3)/P$, the sextic $e^3 A^2 y^2$ becomes

$$
F = A^3 Q + 3 A^2 B H^2 - 3 A B^2 H P + B^3 P^2 - e^3 A P.
$$

Exact factorization of $\operatorname{disc}_s F$ produces the factors listed below. For every nonlinear factor, reduction at the listed test prime preserves the degree and has no root, ruling out rational roots:

| Normalized root | Factor vanishing at $a = 0$ | Other factor degrees (multiplicity, test prime) |
| --- | --- | --- |
| $\alpha$ | $a^6$ | $3\ (6, 7)$, $24\ (1, 5)$ |
| $\alpha^2$ | $a^{12}$ | $3\ (6, 7)$, $9\ (1, 5)$, $33\ (1, 5)$ |

The only possible rational root is $a = 0$, which forces $B = 0$ and drops $x = H/e$ to degree at most $2$. This closes both exceptional normalizations and completes the uniform obstruction. See [cubic_elimination_symmetry.py](cubic_elimination_symmetry.py) for the exact factorizations and residue checks.

## Reproduce the computations

```sh
uv run --with python-flint==0.9.0 cubic_elimination_symmetry.py
uv run --with python-flint==0.9.0 cubic_elimination.py
lake -d .. build CubicEliminant CubicLiftObstruction
```

* **Trust boundary:** The first script enumerates both seeds and checks the Jacobians and exceptional normalizations. The second recomputes both integer discriminants, multiplies their factors back together, and checks the coefficients against the Lean input. Lean verifies that the final polynomial has only the two stated rational roots and excludes $W \equiv 1 \pmod 7$ (and checks the mod-$49$ left-kernel obstructions for $(-2, 3, 1)$). Connecting a candidate substitution to a root of that polynomial relies on the lifting and descent steps written above.
