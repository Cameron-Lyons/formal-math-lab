# Positive-slope cubic charts at 7 for D = 3

For the degree-6 numerators of a cubic Pell substitution through $(0, 1, 1)$ or $(-2, 3, 1)$, exact modular polynomial arithmetic in Python and FLINT rules out balancing slopes $h = 1, 2, 3$ on all 7 normalized residue classes, and rules out 5 of the 7 classes uniformly for all $h \ge 4$. The uniform second-radius proof in [CubicAnnulus.md](CubicAnnulus.md) closes the last two classes as well.

## Coordinates and chart normalization

Put $Q = 1 - Ct^2$ and let $X, Y, Z$ have degree at most 6 with constant terms $(0, 1, 1)$ or $(-2, 3, 1)$. The 18 nonconstant coefficients must solve

$$
F = X^3 + ZY^2 + Z^2 Q^3 - 2 Q^9 = 0.
$$

The positive balancing slope $h$ is the rescaling $t \mapsto 7^h t$ that makes all coefficients 7-integral while keeping at least one nonconstant coefficient a unit. If $h = a/b$ in lowest terms, every surviving positive exponent is divisible by $b$. The exhaustive residue check in [seeded_denominator_lifts.py](seeded_denominator_lifts.py) (which also covers the six classes already excluded modulo 343) finds that the surviving exponents have gcd 1 in every class, so $h$ is an integer.

Before normalizing the chart, the denominator coefficient is $3 \cdot 7^{2h}$. Take the unit $g = X_4 / Y_3$ at the first seed, or at the second seed take $g = X_1$ when $X_1 \not\equiv 0 \pmod 7$ and $g = Y_1$ otherwise. Replacing $t$ by $t/g$ fixes $X_4 = Y_3$ (or sets the chosen linear coefficient to 1) and changes the denominator coefficient to $C = 3 \cdot 7^{2h} / g^2 = 7^{2h} c$ with $c \bmod 7 \in \{3, 5, 6\}$. Because every nonzero square modulo 7 lifts to a square in $\mathbb{Z}_7^\times$, all higher 7-adic digits of $c$ are admissible, so treating $c$ as an arbitrary unit in that class also covers all rational substitutions.

Order the 19 unknowns as $X_1, \dots, X_6, Y_1, \dots, Y_6, Z_1, \dots, Z_6, C$. On each of the 7 charts, the first 15 coefficient equations plus the normalization equation have a 16-by-16 Jacobian minor invertible modulo 7. Let $U, V$ be the deviations of the two listed free $Z$-coefficients from their least nonnegative residues modulo 7; together with $C$, they form three free parameters. Since the 16-by-16 minor is invertible, the remaining 16 coefficients are unique power series in $\mathbb{Z}_7[[U, V, C]]$. Substituting them into $F$ leaves three obstruction series $\Phi_i = [t^i]F$ for $i = 16, 17, 18$.

## Ordinary initial forms

Set $U = 7u$, $V = 7v$, $C = 7c$. The table records the exact orders $d_i$ and the initial **polynomials** $7^{-d_i} \Phi_i(7u, 7v, 7c) \bmod 7$ over $\mathbb{F}_7$. In the associated graded ring of $(7, U, V, C)$, these are dehomogenized by setting the symbol of 7 to 1; rehomogenizing to degree $d_i$ restores powers of that symbol. Each 6-digit string lists $X_1, \ldots, X_6$ modulo 7, with $X_0$ fixed by the seed:

| Chart | Seed | $X_1 \ldots X_6$ | Free $Z$ indices | $L$ | Orders | $\Phi_{16}$ initial | $\Phi_{17}$ initial | $\Phi_{18}$ initial |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | $(0, 1, 1)$ | 000300 | 4, 5 | | 2, 4, 3 | $4c^2$ | $6c^2(u + 4vc + c^2)$ | $4c^3$ |
| 1 | $(-2, 3, 1)$ | 035500 | 5, 6 | $u - v$ | 2, 3, 3 | $c(L - c)$ | $2(L + 3c)(L + 5c)^2$ | $L^3 + 6L^2 c + 5Lc^2 + 6c^3$ |
| 2 | $(-2, 3, 1)$ | 125300 | 4, 6 | $u + 3v + 5$ | 2, 3, 3 | $4c(L - c)$ | $L(L + 4c)^2$ | $L^3 + L^2 c + 5Lc^2 + 4c^3$ |
| 3 | $(-2, 3, 1)$ | 131600 | 5, 6 | $u + v + 6$ | 2, 3, 3 | $6c(L + c)$ | $2L^3 + 2L^2 c + 2L^2 + 5Lc^2 + 3Lc + 4c^3 + 2c^2$ | $6L^3 + 6L^2 c + 2Lc^2 + 6c^3$ |
| 4 | $(-2, 3, 1)$ | 134200 | 5, 6 | | 2, 3, 3 | $5c^2$ | $5c^3$ | $5c^3$ |
| 5 | $(-2, 3, 1)$ | 160000 | 5, 6 | $u + 2v + 3$ | 2, 3, 3 | $3c^2$ | $4L^3 + 4c^3$ | $6L^3 + 3c^3$ |
| 6 | $(-2, 3, 1)$ | 162200 | 5, 6 | | 2, 3, 3 | $5c^2$ | $6c^3$ | $5c^3$ |

## Certificate at positive even denominator valuation

In the table below, set $(U, V, C) = (7u, 7v, 7^w c)$ with $w = 2, 4, 6, 8$ across the four columns. For $h = 1, 2, 3$, keep all $c \in \mathbb{Z}_7$ whose first digit lies in $\{3, 5, 6\}$. For $w = 8$, allow every $c \in \mathbb{Z}_7$ (including $c \equiv 0 \pmod 7$), so a single empty search covers every $h \ge 4$ at once. Each entry is the number of digit levels needed to eliminate all residue boxes:

| Chart | $h = 1$, mod $7^{12}$ | $h = 2$, mod $7^{15}$ | $h = 3$, mod $7^{20}$ | all $h \ge 4$, mod $7^{22}$ |
| --- | ---: | ---: | ---: | ---: |
| 0 | 1 | 3 | 5 | unresolved by this test |
| 1 | 2 | 4 | 6 | 6 |
| 2 | 2 | 4 | 4 | 4 |
| 3 | 2 | 2 | 2 | 2 |
| 4 | 1 | 3 | 5 | unresolved by this test |
| 5 | 1 | 4 | 4 | 4 |
| 6 | 1 | 3 | 3 | 3 |

To compute the polynomial jets modulo $7^N$, the script starts from the mod-7 representatives and iterates Newton correction over $(\mathbb{Z}/7^N)[u, v, c]$ using a fixed lift of the inverse 16-by-16 Jacobian. Whenever the 16 equations vanish modulo $7^n$, one correction step makes them vanish modulo $7^{n+1}$. The script verifies divisibility at every iteration, checks all 16 equations as exact polynomial identities at the end, and cross-checks jets across columns by substituting $c \mapsto 7^{w' - w} c$ and comparing at common precision.

For each of the three remaining series $\Phi_{16}, \Phi_{17}, \Phi_{18}$, divide out the highest common power of 7 visible at that precision and reduce modulo 7 (ignoring any series that vanishes identically at that precision). List all triples $(u, v, c) \in \mathbb{F}_7^3$ satisfying the three reduced equations and the restriction on $c \bmod 7$. For each surviving pair $(a, b)$, substitute $u = a + 7u'$ and $v = b + 7v'$ into the three original jets and recurse while keeping all allowed higher digits of $c$ symbolic. Reaching an empty list proves impossibility at the stated modulus.

The script prints the surviving count of $(u \bmod 7^j, v \bmod 7^j, c \bmod 7)$ at every level. For example, chart 1 ($h \ge 4$) yields $49, 343, 2401, 2401, 16807, 0$, and chart 4 ($h = 3$) yields $18, 126, 294, 2058, 0$. It also checks every ordinary initial form in the first table against independently coded expressions and prints all 21 weighted initial polynomials for $w = 2$:

```bash
uv run --with python-flint==0.9.0 cubic_chart_obstructions.py --forms
```

The only two positive-slope cases left open by this finite test have $h \ge 4$: chart 0 at $(0, 1, 1)$ with $X \equiv 3t^4 \pmod 7$, and chart 4 at $(-2, 3, 1)$ with $X \equiv -2 + t + 3t^2 + 4t^3 + 2t^4 \pmod 7$. Both are closed for every positive slope by the second-radius proof in [CubicAnnulus.md](CubicAnnulus.md).
