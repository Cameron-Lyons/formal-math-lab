# Four record errors in Erdős Problem 311

Extending the record-comparison method from [three consecutive record errors](record-gaps.md) to **four**—and replacing an unweighted product of differences with an optimized weighted product of $14$ linear forms—sharpens the unconditional upper bound on the lower limiting rate $\sigma = \liminf_{N \to \infty} (-\log \delta(N))/N$ below $0.812741$, without assuming a limiting rate exists.

## Main theorem

Let $\delta(N)$ denote the least nonzero distance from $1$ to any sum of distinct reciprocals with denominators in $[1, N]$, and set
$$
\sigma = \liminf_{N \to \infty} \frac{-\log \delta(N)}{N}.
$$
Let $r_*$ be the unique root in $[1, 9/8]$ of the cubic equation
$$
46 r^3 + 169 r^2 - 26 r - 225 = 0.
$$
Then
$$
\sigma \le \frac{5}{2 r_* + 4} \approx 0.812740330896928.
$$
In particular, $\delta(N) > \exp(-0.812741 N)$ for infinitely many $N$.

For comparison, the previous three-record argument gave $0.812742981722\ldots$. Both bounds apply unconditionally; whether a positive limiting rate exists at all remains open. [Problem 311](https://www.erdosproblems.com/311) · [Three-record bound and Sawin's earlier argument](record-gaps.md)

---

## Proof strategy

Just as in the three-record proof, we thin the sequence of record approximations so that each error shrinks by more than a factor of $4$, clear denominators at $X = n_j$ by $L = \operatorname{lcm}(1, \ldots, X)$ to get four integers $(x, y, z, w)$, and compare upper and lower bounds on a carefully chosen product $P$ of linear forms in $x, y, z, w$:
* **Why four records and weighted forms?** Using four records lets us probe primes all the way down to $U/3$ (where $U = n_{j-1}$), splitting $(U/3, X]$ into **five** distinct prime intervals depending on how many multiples of $p$ are available to the older three records (cutoff $\le U$) versus the newest record (cutoff $X$). Weighting $14$ hand-picked linear forms with total degree $48$ maximizes the guaranteed exponent of $p$ dividing $P$ across all five intervals, which can be checked exhaustively over a few hundred residue tuples by a short Python script.

---

## Choosing the errors

Start with $n_1 = 1$ and $\delta(1) = 1$. Recursively define $n_{j+1}$ to be the least index such that
$$
\delta(n_{j+1}) < \frac{\delta(n_j)}{4}.
$$
These indices exist for all $j$ because the power-of-two sums $\sum_{i=1}^k 2^{-i} = 1 - 2^{-k}$ approach $1$ arbitrarily closely. For each $j$, fix an achieving subset $A_j \subseteq [1, n_j]$ and write
$$
u_j = \sum_{a \in A_j} \frac{1}{a} - 1, \qquad |u_j| = \delta(n_j), \qquad H_j = -\log |u_j|.
$$
Thus $u_1 = -1$, and each subsequent $u_j$ carries the sign of its chosen witness. By minimality of $n_{j+1}$, we have $\delta(n_{j+1} - 1) \ge \delta(n_j)/4$. Applying the definition of $\sigma = \liminf (-\log \delta(N))/N$ at $N = n_{j+1} - 1$ gives
$$
H_j \ge (\sigma - o(1)) n_{j+1}.
\tag{1}
$$
The first index admitting four records is $j = 4$; the asymptotic argument uses only the factor-of-$4$ separation between consecutive magnitudes and (1).

Set $X = n_j$, $U = n_{j-1}$, $t = U/X$, and $L = \operatorname{lcm}(1, \ldots, X)$, and define the four integers
$$
(x, y, z, w) = L(u_{j-3}, u_{j-2}, u_{j-1}, u_j).
$$
From the prime number theorem we use $\log L = X + o(X)$ and $\vartheta(s) = \sum_{p \le s} \log p = s + o(s)$.

### Recap of the two-record bound

For each prime $p \in (X/2, X]$, the only positive multiple of $p$ up to $X$ is $p$ itself, so modulo $p$ both $z$ and $w$ lie in $\{0, L/p\}$. Hence at least one of the three nonzero integers $z, w, z - w$ vanishes modulo $p$. Comparing $\prod_{X/2 < p \le X} p$ with $|zw(z - w)| \le 2 L^3 e^{-2 H_{j-1} - H_j}$ gives
$$
2 H_{j-1} + H_j \le \left(\frac{5}{2} + o(1)\right) X.
$$
It suffices to treat the case $\sigma > 4/5$ (since the final bound exceeds $4/5$). By (1), the ratios $n_{j+1}/n_j$ are bounded and their upper limit $r = \limsup_{j \to \infty} n_{j+1}/n_j$ satisfies
$$
1 \le r \le \frac{9}{8}, \qquad \sigma \le \frac{5}{2r + 4}.
\tag{2}
$$
In particular, $t = U/X = n_{j-1}/n_j$ obeys $t \ge 1/r - o(1) \ge 8/9 - o(1)$.

---

## The four-record product

Define $P$ to be the product of the following $14$ linear forms raised to the indicated powers:

| Form | Power | Form | Power |
|---|---:|---|---:|
| $w$ | 4 | $y + z - w$ | 2 |
| $z - w$ | 4 | $x - y - z$ | 1 |
| $z$ | 7 | $x - y$ | 4 |
| $y - z - w$ | 2 | $x - y + z$ | 1 |
| $y - z$ | 6 | $x - z$ | 3 |
| $y - w$ | 2 | $x$ | 3 |
| $y$ | 6 | $x + y - z$ | 3 |

### Upper bound on $\log |P|$

Because $|x| > 4|y| > 16|z| > 64|w| > 0$, in every form above its **earliest** variable in the order $x, y, z, w$ strictly outweighs all subsequent terms combined (for example, $|y| + |z| + |w| < (\frac{1}{4} + \frac{1}{16} + \frac{1}{64})|x| < |x|$). Consequently, every form is nonzero and bounded above in absolute value by twice the magnitude of its earliest variable.

Counting the total power of forms led by each variable:
* Led by $x$: $1 + 4 + 1 + 3 + 3 + 3 = 15$.
* Led by $y$: $2 + 6 + 2 + 6 + 2 = 18$.
* Led by $z$: $4 + 7 = 11$.
* Led by $w$: $4$.

The total degree is $15 + 18 + 11 + 4 = 48$, yielding
$$
\log |P| \le 48 X - 15 H_{j-3} - 18 H_{j-2} - 11 H_{j-1} - 4 H_j + o(X).
\tag{3}
$$

### Normalized residues modulo large primes

Consider any prime $p$ in the range $X/4 < p \le X$. For large $X$, we have $p^2 > X$, so $p$ divides $L$ to the first power only, and $L/p$ is invertible modulo $p$. Multiply all four residues $(x, y, z, w) \bmod p$ by the same invertible unit $6(L/p)^{-1} \bmod p$:
* For an error $u_i$ formed at cutoff $n_i$, the constant term $-L$ and every denominator coprime to $p$ vanish modulo $p$.
* Each selected multiple $bp \le n_i$ (where $1 \le b \le \lfloor n_i/p \rfloor \le 3$) contributes $L/(bp)$, which after multiplying by $6(L/p)^{-1}$ becomes the clean integer $6/b \in \{6, 3, 2\}$!

Therefore, whenever $\lfloor n_i/p \rfloor \le k$, the normalized residue of the $i$th variable has an exact integer representative in the set $H_k$ of subset sums of $\{6/b : 1 \le b \le k\}$:
$$
\begin{aligned}
H_0 &= \{0\}, \\
H_1 &= \{0, 6\}, \\
H_2 &= \{0, 3, 6, 9\}, \\
H_3 &= \{0, 2, 3, 5, 6, 8, 9, 11\}.
\end{aligned}
$$

### Lower bound on $\log |P|$ across five prime ranges

Because the three older records $x, y, z$ use denominators at most $U = n_{j-1}$ while the newest record $w$ uses denominators up to $X = n_j$, the cap tuple $(k_1, k_2, k_3, k_4) = (\lfloor U/p \rfloor, \lfloor U/p \rfloor, \lfloor U/p \rfloor, \lfloor X/p \rfloor)$ changes at the five thresholds $U/3, X/3, U/2, X/2, U, X$.

For each row below, we enumerate all tuples $(a_1, a_2, a_3, a_4) \in H_{k_1} \times H_{k_2} \times H_{k_3} \times H_{k_4}$, sum the powers of all forms in $P$ that vanish identically at $(a_1, a_2, a_3, a_4)$ as integers, and take the minimum over all tuples. Each vanishing form is divisible by $p$, so this minimum is a guaranteed lower bound on the exponent of $p$ in $P$:

| Range of $p$ | $(k_1, k_2, k_3, k_4)$ | Tuples | Minimum exponent |
|---|---|---:|---:|
| $U/3 < p \le X/3$ | $(2, 2, 2, 3)$ | 512 | 1 |
| $X/3 < p \le U/2$ | $(2, 2, 2, 2)$ | 256 | 3 |
| $U/2 < p \le X/2$ | $(1, 1, 1, 2)$ | 32 | 13 |
| $X/2 < p \le U$ | $(1, 1, 1, 1)$ | 16 | 19 |
| $U < p \le X$ | $(0, 0, 0, 1)$ | 2 | 34 |

Since $t = U/X \ge 8/9 - o(1)$, we have $X/4 < U/3 < X/3 < U/2 < X/2 < U < X$ for all sufficiently large $j$, so the five intervals appear in the exact order shown. Because the moving thresholds $U/3, U/2, U$ are bounded above and below by positive constant multiples of $X$, the prime number theorem applies uniformly to each interval. Summing $\log p$ with the five tabulated weights gives
$$
\begin{aligned}
\frac{\log |P|}{X}
&\ge 1\!\left(\frac{1 - t}{3}\right) + 3\!\left(\frac{t}{2} - \frac{1}{3}\right) + 13\!\left(\frac{1 - t}{2}\right) + 19\!\left(t - \frac{1}{2}\right) + 34(1 - t) + o(1) \\
&= \frac{91 - 61t}{3} + o(1).
\end{aligned}
\tag{4}
$$

---

## Optimizing the bound

Pass to a subsequence along which $n_{j+1}/X \to r$, and then to a further subsequence along which $t = U/X \to t_0 \in [1/r, 1]$. Since $n_{j-1}/n_{j-2} \le r + o(1)$, we have $n_{j-2}/X = (n_{j-2}/U)(U/X) \ge t_0/r - o(1)$. By (1), the ratios $H_{j-3}/X, H_{j-2}/X, H_{j-1}/X, H_j/X$ are bounded below (up to $o(1)$) by
$$
\frac{\sigma t_0}{r}, \qquad \sigma t_0, \qquad \sigma, \qquad \sigma r,
$$
respectively. Comparing the upper bound (3) with the lower bound (4) yields
$$
\sigma\!\left(\frac{15 t_0}{r} + 18 t_0 + 11 + 4r\right) \le 48 - \frac{91 - 61 t_0}{3} = \frac{53 + 61 t_0}{3}.
$$
Move the $t_0$-terms to the left-hand side: the coefficient of $t_0$ is $\sigma(15/r + 18) - 61/3$, which is strictly positive whenever $\sigma > 4/5$ and $r \le 9/8$ (indeed, $\frac{4}{5}(\frac{40}{3} + 18) = \frac{4}{5} \cdot \frac{94}{3} = \frac{376}{15} > \frac{61}{3} = \frac{305}{15}$). Thus the inequality is weakest at the smallest possible value $t_0 = 1/r$. Substituting $t_0 \ge 1/r$ and solving for $\sigma$ gives
$$
\sigma \le F(r) := \frac{r(53r + 61)}{3(4r^3 + 11r^2 + 18r + 15)}.
$$

Now compare $F(r)$ with the two-record bound $\frac{5}{2r + 4}$ on $r \in [1, 9/8]$:
* The derivative $F'(r)$ has the sign of the quartic
  $$
  -212 r^4 - 488 r^3 + 283 r^2 + 1590 r + 915,
  $$
  which is strictly positive throughout $[1, 9/8]$—even if we pessimistically evaluate the two negative terms at $r = 9/8$ and the three positive terms at $r = 1$. Hence $F(r)$ is strictly **increasing**.
* The two-record bound $\frac{5}{2r + 4}$ is strictly **decreasing**.
* The two curves cross where $F(r) = \frac{5}{2r + 4}$, which simplifies to
  $$
  46 r^3 + 169 r^2 - 26 r - 225 = 0.
  $$
  This cubic changes sign from $-36$ at $r = 1$ to positive at $r = 9/8$, giving a unique root $r_* \in [1, 9/8]$.

Therefore $\sigma \le \min\bigl(\frac{5}{2r+4}, F(r)\bigr) \le \frac{5}{2r_* + 4}$. Since this common value exceeds $4/5$, the omitted case $\sigma \le 4/5$ before (2) also satisfies the bound. $\square$

---

## Independent verification

Run the following command from the repository root to check all five tuple tables, the algebraic polynomial identities, and the certified rational bracket $0.812740330896927 < 5/(2r_* + 4) < 0.812740330896929$. [Python verifier](verify_four_records.py)

~~~sh
python3 research/erdos-311/verify_four_records.py
~~~
