# Equal LCMs for six consecutive integers

For distinct starts $n < m$, the six-term blocks $\{n+1, \ldots, n+6\}$ and $\{m+1, \ldots, m+6\}$ share the same least common multiple **if and only if**
$$(n, m) \in \{(3, 4),\, (5, 6),\, (13, 15)\}.$$
Every one of these three pairs overlaps, so **disjoint blocks of length six never have equal LCMs**.

**Trust boundary and proof architecture.** The proof combines Lean 4 with a computer-assisted integral-point calculation:
* **Inside Lean 4 ([SixCubics.lean](../SixCubics.lean), [SixElliptic.lean](../SixElliptic.lean)):** the reduction of equal length-6 LCMs to integral points on four plane cubics, the birational maps to four elliptic curves, the deduction of the disjoint-block theorem from the global affine bound, and all finite LCM checks.
* **Outside Lean 4:** full Mordell–Weil bases from `eclib`/`mwrank` and PARI/GP, David’s theorem on linear forms in elliptic logarithms, two-stage LLL lattice reduction using Arb interval arithmetic, and an exact integer-arithmetic point search over the surviving affine box.

An [earlier public write-up](https://erdosproblemaday.com/day/677-lcm-bridge) identified the four cubics and the three overlapping pairs.

## Step 1: Reduction to integral points on four cubics

Set $F(a) = a(a - 1)(a - 3)$, and introduce the triangular-number coordinates
$$a = \binom{n + 4}{2}, \qquad b = \binom{m + 4}{2}.$$
A direct polynomial expansion shows that the six-term product $(n+1)(n+2)\cdots(n+6)$ equals $8 F(a)$! Dividing this product by the block LCM $M(n, 6)$ gives $12 c(n)$, where the auxiliary factor $c(n)$ picks up:
* a factor of $2$ whenever $n \bmod 4 \ge 2$, and
* a factor of $5$ whenever $n \bmod 5 = 4$.

Because $F(a)$ strictly increases with $n$, an equality $M(n, 6) = M(m, 6)$ with $n < m$ forces $F(b)/F(a) = c(m)/c(n) > 1$. Since $c(n) \in \{1, 2, 5, 10\}$, the ratio $u/v = c(m)/c(n) > 1$ can take only **four** values:
$$\frac{u}{v} \in \left\{2,\; \frac{5}{2},\; 5,\; 10\right\}$$
(verified in [SixCubics.lean](../SixCubics.lean)).

## Step 2: From plane cubics to an initial coefficient bound ($M < 10^{400}$)

For each of the four ratios, exact birational formulas send every affine point $(a, b)$ with $ab \ne 0$ to a rational point $P$ on a Weierstrass elliptic curve $E$ ([SixElliptic.lean](../SixElliptic.lean)). All four curves have trivial rational torsion and rank $3$, with a certified full Mordell–Weil basis $G_1, G_2, G_3$.

Write $P = n_1 G_1 + n_2 G_2 + n_3 G_3$ and set $M = \max_i |n_i|$. For any integral point with $|a| \ge 10^8$, $P$ lies close on the real curve to a fixed nonrational algebraic point $Q_\infty$. Measuring distance with the elliptic logarithm (differential $dx/y$), the logarithm difference $L$ satisfies two simultaneous bounds at both ends ($a \ge 10^8$ and $a \le -10^8$) of the real branch ([ellipticGeometry.md](ellipticGeometry.md)):
$$
0 < |L| < \frac{13000}{|a|}, \qquad \log |L| < 19 - \frac{3}{40} M^2.
$$
Pitting this quadratic upper bound against David’s Theorem 2.1 (a lower bound on linear forms in elliptic logarithms) forces the explicit starting cap
$$M < 10^{400}$$
([David.md](David.md)).

> **Historical note.** The elliptic-logarithm method for integral points on plane cubics is due to [Stroeker and de Weger](https://math.deweger.net/papers/%5B29%5DStdW-EllCubic-ActaArith%5B1999%5D.pdf). [Grechuk and Go’s worked certificates](https://github.com/II-eugene-II/diophantine-certificates/releases/tag/v1.1) for other cubics provided a useful model for the David bound and the distance-to-lattice step; the computations here use the models, rank-three bases, target points, and scales tailored to our four curves.

## Step 3: Shrinking $M < 10^{400}$ to an affine bound via LLL

A bound of $10^{400}$ is far too huge to search directly, so we collapse it in two quick stages using **LLL lattice reduction** — turning "the linear form $L$ is tiny" into "a target vector lands unnaturally close to a 4-dimensional integer lattice."

### Computing certified elliptic logarithms

Let $u_1, u_2, u_3, u_\infty \in [0, \omega)$ denote the elliptic logarithms of the three generators and the target point $Q_\infty$, where $\omega > 0$ is the real period (computed with the same differential $dx/y$). All four curves have a single real component. Choosing the integer multiple $m_0 \omega$ that places the representative of $P = \sum n_i G_i$ in $[0, \omega)$ yields
$$
L = n_1 u_1 + n_2 u_2 + n_3 u_3 + m_0 \omega - u_\infty, \qquad |m_0| \le 3M + 2,
$$
because $P$ and $Q_\infty$ lie on the same negative-ordinate branch throughout the tail $|a| \ge 10^8$.

To evaluate $\omega$ and each point logarithm with guaranteed accuracy, write the roots of the minimal-model cubic as $e, w, \bar{w}$ with $e \in \mathbb{R}$. Substituting $X = x + t$ into [Carlson’s defining integral](https://dlmf.nist.gov/19.16.E1) gives
$$\int_x^\infty \frac{dX}{\sqrt{f(X)}} = 2 R_F(x - e, x - w, x - \bar{w}),$$
which equals $\omega / 2$ at $x = e$. Taking this integral when $y > 0$ and subtracting it from $\omega$ when $y < 0$ gives a consistent group logarithm in $[0, \omega)$. The script [logarithms.py](logarithms.py) encloses every integral with Arb ball arithmetic and certifies every rounding step.

### Exact rational distance-to-lattice certificate

Pick a large integer scaling factor $C$, and let $[\cdot]$ denote rounding to the nearest integer. Form the 4-dimensional integer lattice $\Lambda$ generated by the four columns
$$(e_1, [C u_1]), \quad (e_2, [C u_2]), \quad (e_3, [C u_3]), \quad (0, 0, 0, [C\omega])$$
(where $e_1, e_2, e_3$ are the standard basis vectors of $\mathbb{Z}^3$), together with the target vector $t = (0, 0, 0, [C u_\infty])$.

Why does this detect tiny $|L|$? If $M \le M_0$ and $C|L| \le 1$, then the lattice vector $v = n_1(e_1, [Cu_1]) + n_2(e_2, [Cu_2]) + n_3(e_3, [Cu_3]) + m_0(0, 0, 0, [C\omega])$ has first three entries $(n_1, n_2, n_3)$ (squared length $\le 3M_0^2$) and fourth coordinate within $C|L| + \frac{1}{2}(3M_0 + (3M_0 + 2) + 1) < 3M_0 + 3$ of $[Cu_\infty]$. Hence $v$ lies within squared distance
$$\lVert v - t \rVert^2 \le 3M_0^2 + (3M_0 + 3)^2$$
of the target $t$.

To prove **no** lattice vector comes that close, we run LLL to obtain a reduced basis matrix $B$ and check in exact integer arithmetic that the change-of-basis matrix is unimodular (so $B$ generates the exact same lattice $\Lambda$). Then every row $d$ of $B^{-1}$ satisfies $d \cdot v \in \mathbb{Z}$ for all $v \in \Lambda$, so Cauchy–Schwarz gives the purely rational lower bound
$$
\operatorname{dist}(t, \Lambda)^2 \ge
\frac{\operatorname{dist}(d \cdot t, \mathbb{Z})^2}{\lVert d \rVert^2}.
$$
Every step of this inequality is checked in exact rational arithmetic.

### Two reduction stages

At both stages below, the certified lower bound on $\operatorname{dist}(t, \Lambda)^2$ strictly exceeds $3M_0^2 + (3M_0 + 3)^2$, ruling out $C|L| \le 1$:

| Stage | Coefficient bound $M_0$ | Scale $C$ | Bit length of the integer part of the squared-distance lower bound, in ratio order |
| --- | --- | --- | --- |
| 1 | $10^{400}$ | $10^{1800}$ | 2990, 2990, 2990, 2987 |
| 2 | 250 | $10^{16}$ | 24, 24, 25, 25 |

* **Stage 1 ($M < 10^{400} \implies M < 250$):** Ruling out $10^{1800}|L| \le 1$ forces $\log |L| > -1800 \log 10$. Combining with $\log |L| < 19 - \frac{3}{40} M^2$ gives
  $$\frac{3}{40} M^2 < 19 + 1800 \log 10 < 19 + 1800\left(\frac{5}{2}\right) < \frac{3}{40}(250)^2,$$
  so $M < 250$.
* **Stage 2 ($M \le 250 \implies |a| < 13000 \cdot 10^{16}$):** Ruling out $10^{16}|L| \le 1$ forces $|L| > 10^{-16}$. Combining with the real-branch bound $|L| < 13000/|a|$ immediately gives
  $$|a| < 13000 \cdot 10^{16}.$$
  (Every point with $|a| < 10^8$ already satisfies this bound.)

## Step 4: Closing the finite part

* **Disjoint blocks (pure Lean finish):** Given the affine bound alone, Lean converts it into an upper bound on the earlier start $n$ and invokes its finite theorem — requiring no upper bound on the later start $m$ ([SixCubics.lean](../SixCubics.lean), [Height.lean](../Height.lean)).
* **Full classification (exact integer search):** The script [search/SixPoints.py](../search/SixPoints.py) exhaustively searches the signed affine range $|a| \le 10^{21}$ (comfortably covering $13000 \cdot 10^{16}$) in exact integer arithmetic. For each sign of $a$, it bounds a rational approximation to $\sqrt[3]{u/v}$, enumerates every integer pair $(a, b)$ in the resulting strips, and tests the original cubic directly.

Every curve contains the nine trivial root pairs $(a, b) \in \{0, 1, 3\}^2$ (where $F(a) = F(b) = 0$). The complete list of all other integral points is:

| $F(b)/F(a)$ | Other integral points $(a, b)$ | Genuine equal-LCM parameters and common LCM |
| --- | --- | --- |
| 2 | $(13, 16), (36, 45), (136, 171)$ | $(5, 6)$ gives 27,720. $(13, 15)$ gives 1,627,920. |
| 5/2 | $(21, 28)$ | $(3, 4)$ gives 2,520. |
| 5 | None | None |
| 10 | $(17, 35)$ | None |

To recover valid block parameters, $a = \binom{n+4}{2}$ requires $8a + 1 = (2n + 7)^2$ to be a perfect square and $a \ge \binom{4}{2} = 6$:
* $a = 13$ ($8a + 1 = 105$) and $a = 17$ ($8a + 1 = 137$) fail the square test $8a + 1 = \text{square}$.
* The nine root pairs from $\{0, 1, 3\}^2$ fail $\binom{n + 4}{2} \ge 6$.
* The three surviving points $(21, 28)$, $(36, 45)$, and $(136, 171)$ yield precisely $(n, m) \in \{(3, 4), (5, 6), (13, 15)\}$, all of which overlap ([SixCubics.lean](../SixCubics.lean)). $\square$

## Reproduction

From `erdos-677-equal-lcms/`, use the project’s Lean toolchain, PARI/GP 2.19, `eclib` with `mwrank`, and Python with `python-flint==0.9.0`. The standard-library scripts also run with the system Python.

```sh
lake build
gp -fq cubic/ellipticGroups.gp
python -B cubic/ellipticMwrank.py
python -B cubic/ellipticHeight.py
python -B cubic/logarithms.py
python -B search/SixPoints.py --exponent 21
```
