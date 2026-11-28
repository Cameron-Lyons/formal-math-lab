# Elliptic models of the four six-term cubics

Let $F(a) = a(a - 1)(a - 3)$, and consider the four plane cubic curves
$$v F(b) = u F(a), \qquad (u, v) \in \{(2, 1),\, (5, 2),\, (5, 1),\, (10, 1)\},$$
which encode all possible length-6 equal-LCM collisions ([LengthSix.md](LengthSix.md)). Throughout this note, all absolute values are real, all logarithms are natural, and every bound covers **both signs** of $a$.

**What this note proves.** We map each plane cubic into a rank-3 Weierstrass elliptic curve $E(\mathbb{Q})$ with trivial rational torsion and prove two uniform bounds for every integral point $(a, b)$ with $|a| \ge 10^8$:
1. **Real-tail proximity:** the elliptic logarithm difference $L$ between the image point $P = \sum_{i=1}^3 n_i G_i$ and a fixed nonrational algebraic limit point $Q_\infty$ satisfies $0 < |L| < 13000/|a|$.
2. **Quadratic canonical-height bound:** writing $M = \max_i |n_i|$, comparing the naive coordinate height (which grows like $2 \log |a|$) with the Néron–Tate canonical height (which grows at least like $\frac{3}{20} M^2$) yields
   $$\log |L| < 19 - \frac{3}{40} M^2.$$

## From the cubic to a rational elliptic point

For any point with $ab \ne 0$, introduce the slope $t = b/a$. Dividing $vF(b) - uF(a) = 0$ by $a$ collapses the degree-3 equation into a **quadratic in $a$**:
$$
(v t^3 - u)a^2 - 4(v t^2 - u)a + 3(v t - u) = 0.
$$
Set $z = (v t^3 - u)a - 2(v t^2 - u)$. Completing the square eliminates $a$ and produces the quartic model
$$
z^2 = v^2 t^4 + 3uv t^3 - 8uv t^2 + 3uv t + u^2.
$$
Next, define the birational Weierstrass coordinates
$$
x = \frac{2u(z + u) + 3uv t}{t^2}, \qquad
y = \frac{(x^2 - 4u^2 v^2)t - 3uv x - 6u^3 v}{2u}.
$$
Substituting shows that $(x, y)$ lies on the Weierstrass cubic
$$
E:\quad y^2 = f(x) = x^3 - 8uv x^2 + 5u^2 v^2 x + 9u^4 v^2 + 9u^2 v^4 + 32u^3 v^3.
$$
Lean checks all of these algebraic identities in [SixElliptic.lean](../SixElliptic.lean). The minimal Weierstrass models are obtained by the integer shift $X = x - s$, $Y = y$, with $s = 5, 27, 13, 27$ for $(u, v) = (2, 1), (5, 2), (5, 1), (10, 1)$, respectively. Note that image points $(X, Y) \in E(\mathbb{Q})$ can have nontrivial denominators; mapping into $E(\mathbb{Q})$ is still all we need to bound every *integral* plane point $(a, b)$.

## Uniform real tail for $|a| \ge 10^8$

**Intuition.** As $A = |a| \to \infty$, the leading terms of $v F(b) = u F(a)$ behave like $v b^3 \approx u a^3$, forcing the slope $t = b/a$ to hug $\alpha = (u/v)^{1/3}$ within $O(1/A)$. Consequently, the image point $(x, y)$ stays within $O(1/A)$ of a fixed irrational point $(x_\infty, y_\infty)$ on the real curve.

1. **Coarse slope bracket ($1 < t < 3$).** Put $A = |a| \ge 10^8$ and $\alpha = (u/v)^{1/3}$.
   * *Case $a > 0$:* Above $3$, $F$ is strictly increasing with $F(a) > 0$ and $F(3a) > 10 F(a) \ge (u/v) F(a) = F(b) > F(a)$, forcing $a < b < 3a$.
   * *Case $a < 0$:* Here $F(b) = (u/v) F(a) < F(a) < -10^6$, which forces $b < 0$. On $(-\infty, 0)$, $F$ is strictly increasing and $F(3a)/F(a) = 3(3A + 1)(3A + 3)/((A + 1)(A + 3)) > 10$ for all $A \ge 10$, giving $3a < b < a$.

   In both cases, $1 < t < 3$.
2. **Tight slope approximation ($|t - \alpha| < 27/A$).** Rewriting the quadratic relation in $a$ as $t^3 - \alpha^3 = 4(t^2 - \alpha^3)/a - 3(t - \alpha^3)/a^2$ and using $1 < t < 3$ and $\alpha^3 \le 10$ gives
   $$
   |t^3 - \alpha^3| \le \frac{4(9 + 10)}{A} + \frac{3(3 + 10)}{A^2} < \frac{80}{A}.
   $$
   Since $t, \alpha > 1$, we have $t^2 + t\alpha + \alpha^2 > 3$, and dividing by $t^2 + t\alpha + \alpha^2$ gives
   $$
   |t - \alpha| < \frac{27}{A}.
   $$
3. **Proximity of $x$ to the irrational limit $x_\infty$.** Solving the quadratic relation for $(v t^3 - u)a$ and substituting into $z$ and $x$ yields
   $$
   x = g(t) - \frac{6u(vt - u)}{a t^2}, \qquad
   g(t) = 4uv - \frac{2u^2}{t^2} + \frac{3uv}{t}.
   $$
   On $1 \le t \le 3$, one checks $|g'(t)| \le 430$ and $|6u(vt - u)/(a t^2)| \le 960/A$. Combining with $|t - \alpha| < 27/A$ gives
   $$|x - x_\infty| < \frac{13000}{A}, \qquad x_\infty = g(\alpha).$$
   Define $y_\infty = y(x_\infty, \alpha)$ via the displayed formula for $y$. Specializing the quartic identity to $t = \alpha$ and $z = 2(v\alpha^2 - u)$ (using $v\alpha^3 = u$) confirms that $(x_\infty, y_\infty)$ lies on $E$. Writing $\beta = v\alpha$, we have
   $$x_\infty = 4uv - 2u\beta + 3\beta^2.$$
   Because $u/v$ is a noncube rational, $\beta$ has algebraic degree $3$ over $\mathbb{Q}$, so $x_\infty \notin \mathbb{Q}$. In particular, no rational point $(x, y)$ can equal $(x_\infty, y_\infty)$, guaranteeing $L \ne 0$.
4. **Same real branch and integral bound.** Rational interval arithmetic in `ellipticHeight.py` proves $7 < x_\infty < 36$ and $y_\infty < -9$ in all four cases. Along the segment between $x$ and $x_\infty$, we have $|x| < 41$ and $|f'(x)| < 13000$, which forces
   $$f(x) > 81 - \frac{13000^2}{10^8} > 1.$$
   On the corresponding $(x, t)$-rectangle, $|\partial y / \partial x| < 126$ and $|\partial y / \partial t| < 1041$, yielding $|y - y_\infty| < 2 \cdot 10^6 / A$. Thus both $(x, y)$ and $(x_\infty, y_\infty)$ lie on the **same negative-$y$ branch**, where $|y| = \sqrt{f(x)} > 1$. Integrating along that branch gives a nonzero elliptic logarithm difference $L$ (up to a real period) satisfying
   $$
   0 < |L| < \frac{13000}{A}
   $$
   for either $dx/(2y)$ or $dx/y$. Reversing both orientations preserves this bound.

## Canonical heights and the analytic bound

**The bridge between $\log A$ and $M^2$.** The naive coordinate height $h(X(P))$ is easy to bound above in terms of $\log A$, while the Néron–Tate canonical height $H(P)$ is a positive-definite quadratic form on the Mordell–Weil lattice $\mathbb{Z} G_1 \oplus \mathbb{Z} G_2 \oplus \mathbb{Z} G_3$ (hence bounded below by a multiple of $M^2$). Bounding the difference $|H(P) - h(X(P))|$ connects $M^2$ directly to $\log A$, and therefore to $\log |L|$.

1. **Difference between naive and canonical heights.** For reduced rational coordinates, write $h(p/q) = \log\max(|p|, |q|)$, set $h(X(O)) = 0$, and define the canonical height on the minimal model by
   $$H(P) = \lim_{j \to \infty} 4^{-j} h(X(2^j P)).$$
   On $Y^2 = X^3 + cX^2 + dX + e$, the $X$-coordinate of $2P$ is the ratio $D_1(p, q) / D_2(p, q)$ of two homogeneous duplication quartics:
   $$
   \begin{aligned}
   D_1(p, q) &= p^4 - 2d p^2 q^2 - 8e p q^3 + (d^2 - 4ce)q^4, \\
   D_2(p, q) &= 4p^3 q + 4c p^2 q^2 + 4d p q^3 + 4e q^4.
   \end{aligned}
   $$
   * *Upper bound:* `ellipticHeight.py` checks that the coefficient sums of $D_1$ and $D_2$ are at most $2^{42} < e^{30}$, giving $h(X(2P)) - 4h(X(P)) < 30$.
   * *Lower bound:* To control possible cancellation between $D_1(p, q)$ and $D_2(p, q)$, the script verifies explicit integer homogeneous identities $D T^7 = B_1 D_1 + B_2 D_2$ for both $T = p$ and $T = q$, using a common positive integer $D$ and homogeneous cubics $B_1, B_2$ whose combined coefficient sum is at most $2^{142} < e^{100}$. Thus $\gcd(D_1, D_2) \mid D$ whenever $\gcd(p, q) = 1$. Applying the identity to the larger of $|p|, |q|$ proves
     $$
     -100 < h(X(2P)) - 4h(X(P)) < 30.
     $$
   Iterating and summing the geometric series $\sum_{j \ge 1} 4^{-j} = 1/3$ yields
   $$h(X(P)) - \frac{100}{3} \le H(P) \le h(X(P)) + 10.$$
2. **Lowest eigenvalue of the height Gram matrix.** For each full Mordell–Weil basis $G_1, G_2, G_3$ in the table below, `ellipticHeight.py` performs six exact doublings at every $G_i$ and $G_i + G_j$ to enclose each canonical height within $100/(3 \cdot 4^6)$ plus logarithm rounding. Polarization produces rigorous interval enclosures for the canonical height Gram matrix, and interval determinants combined with Sylvester’s criterion place all of its eigenvalues strictly between $3/20$ and $4$. In particular, for every nonzero point $P = \sum_{i=1}^3 n_i G_i$ with $M = \max_i |n_i|$,
   $$H(P) > \frac{3}{20} M^2.$$
3. **Naive height in terms of $A$, and the final bound.** Writing $X = x - s$ directly in terms of $a$ and $b$ gives
   $$
   X = \frac{(4uv - s)b^2 + 3uv ab - 2u^2 a^2 - 6uv b + 6u^2 a}{b^2}.
   $$
   For $1 < t < 3$, the script checks in each case that both the numerator magnitude and the denominator stay strictly below $2048 A^2$. Reducing the fraction can only decrease the height, so $h(X(P)) < 2 \log A + 8$ (as $\log 2048 < 8$) and therefore
   $$H(P) < 2 \log A + 18.$$
   Comparing $\frac{3}{20} M^2 < H(P) < 2 \log A + 18$ gives $\log A > \frac{3}{40} M^2 - 9$. Substituting this into the real-tail bound $\log |L| < \log(13000) - \log A < 10 - \log A$ yields
   $$
   \log |L| < 19 - \frac{3}{40} M^2.
   $$

## Reproducing the arithmetic

| $u/v$ | Minimal $(a_2, a_4, a_6)$, $a_1 = a_3 = 0$ | Full basis $(X, Y)$ |
| --- | --- | --- |
| 2 | $(-1, -65, 261)$ | $(5, -6), (-7, 18), (-4, 21)$ |
| 5/2 | $(1, -1633, 32963)$ | $(23, -90), (-37, 210), (-31, 234)$ |
| 5 | $(-1, -408, 6912)$ | $(-24, 48), (12, -60), (-18, 90)$ |
| 10 | $(1, -1633, 97763)$ | $(-58, 27), (23, -270), (-37, 330)$ |

Run these commands from `erdos-677-equal-lcms/`:

```sh
lake env lean SixElliptic.lean
gp -fq cubic/ellipticGroups.gp
python -B cubic/ellipticMwrank.py
python cubic/ellipticHeight.py
```

[PARI/GP’s elliptic-curve routines](https://pari.math.u-bordeaux.fr/dochtml/html/Elliptic_curves.html) verify minimal models, conductors, trivial rational torsion, ranks, and membership of the generators. The Python wrapper runs `mwrank -p 180 -S -1` from [eclib](https://github.com/JohnCremona/eclib) separately on each model, checks that eclib reports an unconditional full Mordell–Weil basis, and compares the returned basis against the table above (set `MWRANK` to the executable path if needed). The height and tail verifier (`cubic/ellipticHeight.py`) uses only Python’s standard library.
