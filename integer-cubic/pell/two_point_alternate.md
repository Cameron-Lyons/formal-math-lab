# The two marked points force integrality at 7

Let $x, y, z$ be rational polynomials on $u^2 - 3v^2 = 1$ of total degrees at most $(4, 3, 6)$ satisfying $z^2 + y^2 z + x^3 = 2$ identically. Suppose they take $(0, 1, 1)$ at $(1, 0)$ and either $(1, 0, -1)$ or $(-2, 3, 1)$ at $(2, 1)$. **Every coefficient in the $(w, v)$ chart below must be integral at 7**, even when arbitrary powers of 7 are allowed in denominators.

Set $w = u - 1 - v$, which vanishes at both marked points ($v = 0$ at $(1, 0)$ and $v = 1$ at $(2, 1)$). The conic relation becomes

$$
v^2 = (1 + w)v + w + \frac{w^2}{2}.
$$

Reducing repeatedly by this monic relation writes each coordinate of degree bound $d$ uniquely as $P(w) + vQ(w)$ with $\deg P \le d$ and $\deg Q < d$. Since the marked values specify $P(0)$ and $P(0) + Q(0)$, both $P(0)$ and $Q(0)$ are integers.

Suppose some coefficient has negative 7-adic valuation, and let $h = \max(-v_7(a_i)/i) > 0$ over all nonzero positive-degree coefficients of the six polynomials. Pick $\delta$ with $v_7(\delta) = h$ in a totally ramified extension (whose residue field stays $\mathbb{F}_7$) and substitute $w = \delta s$. All rescaled coefficients become 7-integral with at least one unit positive-degree coefficient, and the conic relation reduces to $v^2 = v$. Evaluating at $v = 0$ and $v = 1$ gives two ordinary polynomial triples $A = P$ and $B = P + Q$ over $\mathbb{F}_7[s]$ hitting the two marked values, with at least one nonconstant. Because each $Q$ has smaller degree than $P$, the top coefficients (at $s^4, s^3, s^6$) agree between $A$ and $B$.

[two_point_alternate.py](two_point_alternate.py) runs an exhaustive census over all $7^4$ choices of positive-degree coefficients of $x$. If $x$ is constant, then $z(z + y^2) = 2 - x^3$ is a nonzero constant at all three seeds, forcing $y$ and $z$ constant too. For each nonconstant $x$, the script factors $2 - x^3$, lists all monic divisors where both the divisor and cofactor have degree at most 6, fixes the scalar using $z(0)$, and checks whether their difference is a square of degree at most 6 (testing both signs of the square root, and keeping constant solutions when matching top coefficients):

| Second marked value | Nonconstant triples at the second mark | Compatible nonconstant pairs | Jacobian rank | Augmented rank |
| --- | ---: | ---: | ---: | ---: |
| $(1, 0, -1)$ | 18 | 6 | 19 | 20 |
| $(-2, 3, 1)$ | 42 | 6 | 18 | 19 |

There are 6 nonconstant triples at the first mark. In both rows of the table, all 6 compatible pairs form a single orbit under $s \mapsto as$ ($a \in \mathbb{F}_7^\times$), and in every pair $P_x$ and $P_y$ keep degrees 4 and 3. Before rescaling, their leading coefficients are rational numbers of valuations $-4h$ and $-3h$, so $4h, 3h \in \mathbb{Z}$ and hence $h \in \mathbb{Z}$. We can therefore pick a rational $\delta$ of valuation $h$ whose unit factor moves the pair to the orbit representative with top coefficients $(3, 3, 2)$.

Now write $w = 2Hs$ with $7 \mid H$ in $\mathbb{Z}_7$, so the exact relation is

$$
v^2 = (1 + 2Hs)v + 2Hs + 2H^2 s^2.
$$

There are 24 unknowns (23 positive-degree coefficients plus $H$) and 23 nonconstant coefficient equations (12 in the constant component and 11 in the $v$-component). For each of the two orbit representatives, a linear combination of the 23 equations has a constant term nonzero modulo 49 while all 24 first-order correction coefficients vanish modulo 49 (and higher-order terms are automatically divisible by 49). Neither representative lifts, contradicting negative 7-adic valuation. Lean certifies both obstructions in [two_point_alternate.lean](two_point_alternate.lean).

Substituting into the rational chart $L = 1 - 3t^2$, $u = (1 + 3t^2)/L$, $v = 2t/L$ yields 7-integral numerator coefficients, so the complete mod-7 two-point census covers every rational substitution under these hypotheses.

## The alternate endpoint at 2

When the coefficients in the original Pell ring are 2-integral, each coordinate writes uniquely as

$$
f = A + (B - A)v + v(v - 1)R(v) + wQ(v), \qquad w = u - 1 - v,
$$

where $A, B$ are its two marked values, $\deg R \le d - 2$, and $\deg Q < d$. Reducing via $w^2 = 2(v^2 - v) - 2(1 + v)w$ preserves 2-integrality, and conversely $P(v) - A - (B - A)v$ is divisible by the monic polynomial $v(v - 1)$ whenever $P$ matches both marks.

For $(A_x, A_y, A_z) = (0, 1, 1)$ and $(B_x, B_y, B_z) = (-2, 3, 1)$, an explicit choice of the 23 free coefficients solves the surface identity modulo 2048, while no assignment solves it modulo 4096. Thus 4096 is the first obstructing power of 2. In [two_point_alternate_two.lean](two_point_alternate_two.lean), Lean checks the mod-2048 witness by computation and proves the mod-4096 impossibility using bit-vector arithmetic.

Finally, the 2-adic balancing argument in [TwoPointAlternateTwo.md](TwoPointAlternateTwo.md) forces every rational candidate for this alternate pair of marks into the original 2-integral lattice. Together, these results rule out that quartic ansatz for arbitrary rational coefficients.
