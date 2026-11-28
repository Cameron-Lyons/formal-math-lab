# Positive-slope cubic charts at 7 for $D = 3$

This note records an explicit $7$-adic implicit-function computation for degree-6 numerators of a cubic Pell substitution on $u^2 - 3v^2 = 1$ through either $(0, 1, 1)$ or $(-2, 3, 1)$ when the coefficients have $7$ in their denominators (a **positive balancing slope** $h > 0$).

Using exact modular polynomial arithmetic in Python and FLINT, this calculation rules out:

* balancing slopes $h = 1, 2, 3$ on **all $7$** normalized residue classes, and
* **all $h \ge 4$ uniformly** on $5$ of the $7$ classes.

The uniform second-radius proof in [CubicAnnulus.md](CubicAnnulus.md) subsequently closed the last two classes (charts $0$ and $4$ for $h \ge 4$) as well.

## Big idea: $7$-adic implicit charts and obstruction series

Suppose $(X, Y, Z)$ solves the balanced cubic Pell system modulo $7$ after rescaling $t \mapsto 7^h t$. That system has $19$ unknowns (the $18$ nonconstant coefficients of $X, Y, Z$ plus the rescaled denominator coefficient $C$) constrained by $18$ polynomial equations plus $1$ chart-normalization equation.

On each of the $7$ normalized residue classes modulo $7$, a $16 \times 16$ Jacobian minor turns out to be invertible modulo $7$. By the multivariate $7$-adic implicit function theorem, we can solve $16$ of the $19$ equations uniquely for $16$ unknowns as power series in the remaining **three free parameters** $(U, V, C)$. Substituting those power series into the last three equations leaves just **three obstruction series** $\Phi_{16}, \Phi_{17}, \Phi_{18} \in \mathbb{Z}_7[[U, V, C]]$ whose simultaneous vanishing is necessary for a lift to exist. Computing polynomial truncations ("jets") of $\Phi_{16}, \Phi_{17}, \Phi_{18}$ modulo $7^N$ and subdividing the $(U, V)$-box digit by digit proves that no $7$-adic zero exists.

## Coordinates and chart normalization

Put $Q = 1 - Ct^2$ and let $X, Y, Z$ have degree at most $6$ with constant terms $(0, 1, 1)$ or $(-2, 3, 1)$. The $18$ nonconstant coefficients must satisfy

$$
F = X^3 + ZY^2 + Z^2 Q^3 - 2 Q^9 = 0.
$$

### Why the balancing slope $h$ is an integer

The positive balancing slope $h$ is defined so that the rescaling $t \mapsto 7^h t$ makes all coefficients $7$-integral while keeping at least one nonconstant coefficient a $7$-adic unit. If $h = a/b$ in lowest terms, then any term $f_i t^i$ whose rescaled valuation hits $0$ must satisfy $v_7(f_i) + ia/b = 0$, forcing $b \mid i$; hence every surviving positive exponent modulo $7$ is divisible by $b$. The exhaustive residue check in [seeded_denominator_lifts.py](seeded_denominator_lifts.py) (which also covers the six classes already excluded modulo $343$) finds that the surviving exponents have $\gcd = 1$ in every class, so **$h$ must be a positive integer**.

### Normalizing the chart and tracking the square class of $C$

Before normalizing, the rescaled denominator coefficient is $3 \cdot 7^{2h}$. We fix the scaling freedom $t \mapsto t/g$ using a $7$-adic unit $g$:

* at the first seed $(0, 1, 1)$, take $g = X_4 / Y_3$ (fixing $X_4 = Y_3$);
* at the second seed $(-2, 3, 1)$, take $g = X_1$ when $X_1 \not\equiv 0 \pmod 7$, and $g = Y_1$ otherwise (setting the chosen linear coefficient to $1$).

Replacing $t$ by $t/g$ changes the denominator coefficient to

$$
C = \frac{3 \cdot 7^{2h}}{g^2} = 7^{2h} c.
$$

Since the nonzero squares modulo $7$ are $\{1, 2, 4\}$, the quotients $3/g^2 \bmod 7$ range over the three nonsquares $\{3, 5, 6\}$. By Hensel's lemma, every nonzero square modulo $7$ lifts to a square in $\mathbb{Z}_7^\times$, so all higher $7$-adic digits of $c$ are admissible. Treating $c$ as an arbitrary $7$-adic unit with $c \bmod 7 \in \{3, 5, 6\}$ therefore covers every rational substitution.

### Compressing $19$ variables to $3$ free parameters

Order the $19$ unknowns as $X_1, \dots, X_6, Y_1, \dots, Y_6, Z_1, \dots, Z_6, C$. On each of the $7$ charts, the first $15$ coefficient equations $[t^1]F = \dots = [t^{15}]F = 0$ together with the single normalization equation have a $16 \times 16$ Jacobian minor that is invertible modulo $7$.

Let $U, V$ be the deviations of the two listed free $Z$-coefficients from their least nonnegative residues modulo $7$; together with $C$, they form three free parameters. Because the $16 \times 16$ minor is invertible, the remaining $16$ coefficients are uniquely determined as power series in $\mathbb{Z}_7[[U, V, C]]$. Substituting them into $F$ leaves three obstruction series:

$$
\Phi_i = [t^i]F \in \mathbb{Z}_7[[U, V, C]] \qquad (i = 16, 17, 18).
$$

## Ordinary initial forms

To inspect the leading behavior of $\Phi_{16}, \Phi_{17}, \Phi_{18}$, set $U = 7u$, $V = 7v$, $C = 7c$. The table below records the exact orders $d_i$ (the highest power of $7$ dividing $\Phi_i(7u, 7v, 7c)$ identically) and the resulting initial **polynomials** $7^{-d_i} \Phi_i(7u, 7v, 7c) \bmod 7$ over $\mathbb{F}_7$. In the associated graded ring of $(7, U, V, C)$, these are dehomogenized by setting the symbol of $7$ to $1$; rehomogenizing to degree $d_i$ restores powers of that symbol. Each 6-digit string lists $X_1, \ldots, X_6$ modulo $7$, with $X_0$ fixed by the seed:

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

Because $C = 7^{2h} c$ always carries an **even** power of $7$, we substitute $(U, V, C) = (7u, 7v, 7^w c)$ with $w = 2, 4, 6, 8$ across the four columns of the table below:

* For $h = 1, 2, 3$ ($w = 2, 4, 6$), we keep all $c \in \mathbb{Z}_7$ whose first digit lies in $\{3, 5, 6\}$.
* For $w = 8$, we allow **every** $c \in \mathbb{Z}_7$ (including $c \equiv 0 \pmod 7$). Because any $C = 7^{2h} c'$ with $h \ge 4$ has the form $7^8 c$ for some $c \in \mathbb{Z}_7$, a single empty search at $w = 8$ rules out **every $h \ge 4$ simultaneously**.

Each table entry reports how many digit levels were needed to eliminate all residue boxes:

| Chart | $h = 1$, mod $7^{12}$ | $h = 2$, mod $7^{15}$ | $h = 3$, mod $7^{20}$ | all $h \ge 4$, mod $7^{22}$ |
| --- | ---: | ---: | ---: | ---: |
| 0 | 1 | 3 | 5 | unresolved by this test |
| 1 | 2 | 4 | 6 | 6 |
| 2 | 2 | 4 | 4 | 4 |
| 3 | 2 | 2 | 2 | 2 |
| 4 | 1 | 3 | 5 | unresolved by this test |
| 5 | 1 | 4 | 4 | 4 |
| 6 | 1 | 3 | 3 | 3 |

### How the jets and box elimination are certified

1. **Exact Newton lifting of the polynomial jets:** To compute the implicit power series modulo $7^N$, the script starts from the mod-$7$ representatives and iterates Newton correction over $(\mathbb{Z}/7^N)[u, v, c]$ using a fixed lift of the inverse $16 \times 16$ Jacobian. Whenever the $16$ defining equations vanish modulo $7^n$, one correction step makes them vanish modulo $7^{n+1}$. The script verifies divisibility at every iteration, confirms all $16$ equations as exact polynomial identities at the end, and cross-checks jets across columns by substituting $c \mapsto 7^{w' - w} c$ and comparing at common precision.
2. **Recursive box elimination:** For each of the three remaining series $\Phi_{16}, \Phi_{17}, \Phi_{18}$, divide out the highest common power of $7$ visible at that precision and reduce modulo $7$ (ignoring any series that vanishes identically at that precision). List all triples $(u, v, c) \in \mathbb{F}_7^3$ satisfying the three reduced equations and the restriction on $c \bmod 7$. For each surviving pair $(a, b)$, substitute $u = a + 7u'$ and $v = b + 7v'$ into the three original jets and recurse while keeping all allowed higher digits of $c$ symbolic. Reaching an empty list proves impossibility at the stated modulus.

The script prints the surviving count of $(u \bmod 7^j, v \bmod 7^j, c \bmod 7)$ at every level. For example, chart $1$ ($h \ge 4$) yields $49, 343, 2401, 2401, 16807, 0$, and chart $4$ ($h = 3$) yields $18, 126, 294, 2058, 0$. It also checks every ordinary initial form in the first table against independently coded expressions and prints all $21$ weighted initial polynomials for $w = 2$:

```bash
uv run --with python-flint==0.9.0 cubic_chart_obstructions.py --forms
```

The only two positive-slope cases left open by this finite test have $h \ge 4$:

* **Chart $0$** at $(0, 1, 1)$, with $X \equiv 3t^4 \pmod 7$;
* **Chart $4$** at $(-2, 3, 1)$, with $X \equiv -2 + t + 3t^2 + 4t^3 + 2t^4 \pmod 7$.

Both are closed unconditionally for every positive slope by the second-radius proof in [CubicAnnulus.md](CubicAnnulus.md).
