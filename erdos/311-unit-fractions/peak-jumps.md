# How accurate approximations constrain individual jumps

Could $-\log \delta(n)/n$ reach a high peak rate—say $4/5$, or anything above Will Sawin's conditional ceiling $C \approx 0.693$—purely through tiny, gradual single-step gains? **No.** Any peak exponential rate strictly above $C$ forces occasional *macroscopic* single-step jumps where $\log(\delta(n-1)/\delta(n))$ is a constant multiple of $n$! Conversely, if all single-step logarithmic gains are $o(n)$, then $\limsup (-\log \delta(n))/n \le C$ holds unconditionally, without ever assuming that $-\log \delta(n)/n$ converges to a limit.

## Setup and main results

Let $H_n = -\log \delta(n)$ for the least nonzero distance to $1$, and define the upper limiting rate $\tau$ and the maximum linear single-step jump $\gamma$:
$$
\tau = \limsup_{n \to \infty} \frac{H_n}{n}, \qquad
\gamma = \limsup_{n \to \infty} \frac{H_n - H_{n-1}}{n}.
$$
Let $s_k = |E_k|$ be the number of distinct rational subset sums using $\{1, 1/2, \ldots, 1/k\}$ (for example, $s_1 = 2$ for $\{0, 1\}$, and $s_2 = 4$ for $\{0, 1/2, 1, 3/2\}$), and define Sawin's constant
$$
C = 1 - \sum_{k \ge 1} \frac{1}{k(k+1) s_k} \approx 0.693.
$$

**Theorem.**
1. If $\tau \ge 4/5$, then $\gamma \ge 2/175$.
2. More generally, whenever $\tau > C$,
   $$
   \gamma \ge \frac{3(\tau - C)^2}{8C}.
   $$
   In particular, if $H_n - H_{n-1} = o(n)$ (i.e., $\gamma = 0$), then $\tau \le C$ unconditionally.

The constant $C$ is the exact constant from Will Sawin's conditional upper bound (which assumes $H_n/n$ converges). The proof below adapts the same collision-counting idea across multiple record errors, while tracking how much accuracy can be lost across $m$ consecutive jumps via $\gamma$. [Sawin's discussion](https://www.erdosproblems.com/forum/thread/311)

---

## Comparing the last several distinct minima

**The big idea.** Take a large $N$ where $H_N/N \approx \tau$, and collect the $m$ most recent distinct record errors $u_1, \ldots, u_m$ up to $N$ (with $u_1$ the most accurate). Multiplying by $L = \operatorname{lcm}(1, \ldots, N)$ gives $m + 1$ distinct integers $0, Lu_1, \ldots, Lu_m$. Form the product $V$ of *all* $\binom{m+1}{2}$ pairwise differences between these integers:
* **Upper bound on $V$:** Each error $u_i$ is at most $i - 1$ jumps older than $u_1$, so $-\log|u_i| \ge H_N - (i - 1)\gamma N - o(N)$. That makes $V$ exponentially small compared to $L^{\binom{m+1}{2}}$—unless $\gamma$ is large!
* **Lower bound on $V$:** For each prime $p \in (N/(k+1), N/k]$, the integers $0, Lu_1, \ldots, Lu_m$ can hit at most $s_k$ residue classes modulo $p$. By the pigeonhole principle, at least $v(s_k, m+1)$ pairs must collide modulo $p$, supplying $p^{v(s_k, m+1)} \mid V$.

Playing the upper bound off the lower bound directly ties $\tau$ to $\gamma$!

### Minimum number of collisions $v(s, t)$

Fix an integer $m \ge 2$ and write $D = \binom{m+1}{2}$. For integers $s, t \ge 1$, put
$$
v(s, t) = s \binom{a}{2} + ab, \qquad \text{where } a = \lfloor t/s \rfloor,\quad b = t - as.
$$
By convexity of $x \mapsto \binom{x}{2}$, $v(s, t)$ is the **minimum number of equal pairs** when $t$ items are placed into $s$ bins—attained when $b$ bins have size $a + 1$ and $s - b$ bins have size $a$, giving $b\binom{a+1}{2} + (s-b)\binom{a}{2} = s\binom{a}{2} + ab$.

*Sanity check:* For $m = 6$ ($t = 7$ items):
* With $s = 2$ bins, the most balanced split is $4 + 3$, giving $v(2, 7) = \binom{4}{2} + \binom{3}{2} = 6 + 3 = 9$ colliding pairs.
* With $s = 4$ bins, the most balanced split is $2 + 2 + 2 + 1$, giving $v(4, 7) = 3\binom{2}{2} + \binom{1}{2} = 3$ colliding pairs.

### Key inequality

**Proposition.** For every fixed integer $m \ge 2$,
$$
\tau \le 1 - \frac{1}{D} \sum_{k \ge 1} \frac{v(s_k, m + 1)}{k(k + 1)} + \frac{2(m - 1)}{3}\,\gamma.
\tag{1}
$$
(Note that only finitely many terms in the sum are nonzero, since $s_k \ge k + 1$ implies $v(s_k, m + 1) = 0$ as soon as $k \ge m$.)

**Proof.**
1. **Pick the last $m$ distinct minima.** Let $N \to \infty$ along a subsequence with $H_N/N \to \tau$. Choose signed attainable errors $u_1, \ldots, u_m$ realizing the $m$ smallest distinct values of $\delta(n)$ up to $N$, ordered most accurate first:
   $$
   0 < |u_1| < |u_2| < \cdots < |u_m|.
   $$
   At least $m$ distinct minima exist once $N$ is large (since the dyadic sums $1 - 2^{-k}$ approach $1$ strictly monotonically). All $m$ errors are attainable at cutoff $N$.

   To pass from $u_1$ back to $u_i$, we step backward across exactly $i - 1$ strict jumps, each occurring at some index $n \le N$ whose location tends to $\infty$ as $N \to \infty$. Since $\gamma$ is finite (as $H_n \le \log \operatorname{lcm}(1, \ldots, n) = n + o(n)$), each backward jump drops $H$ by at most $(\gamma + o(1))N$, yielding
   $$
   -\log |u_i| \ge H_N - (i - 1)(\gamma + o(1)) N \qquad (1 \le i \le m).
   $$

2. **Upper bound on the pairwise difference product $V$.** Put $L = \operatorname{lcm}(1, \ldots, N)$ and define $V$ to be the absolute product of all $D = \binom{m+1}{2}$ pairwise differences among the $m + 1$ distinct integers $0, Lu_1, \ldots, Lu_m$:
   $$
   V = \prod_{1 \le i \le m} |Lu_i| \cdot \prod_{1 \le r < i \le m} |Lu_i - Lu_r|.
   $$
   For each $1 \le i \le m$, there are exactly $i$ earlier entries ($0, Lu_1, \ldots, Lu_{i-1}$), each strictly smaller in magnitude than $|Lu_i|$, so every one of those $i$ differences has absolute value at most $2 L |u_i|$. Taking logarithms and using $\log L = N + o(N)$, $H_N = (\tau + o(1))N$, and the identity $\sum_{i=1}^m i(i - 1) = \frac{1}{3}(m-1)m(m+1) = \frac{2}{3} D(m - 1)$ gives
   $$
   \begin{aligned}
   \log V &\le \sum_{i=1}^m i \bigl(\log(2L) + \log |u_i|\bigr) \\
          &\le D N \bigl(1 - \tau + o(1)\bigr) + \sum_{i=1}^m i(i - 1)(\gamma + o(1)) N \\
          &= D N \left(1 - \tau + \frac{2(m - 1)}{3}\gamma + o(1)\right).
   \end{aligned}
   $$

3. **Lower bound on $V$ from modulo-$p$ collisions.** Fix any $k \ge 1$ with $s_k < m + 1$, and consider any prime $p$ in the interval
   $$
   \frac{N}{k + 1} < p \le \frac{N}{k}.
   $$
   For large $N$, we have $p^2 > N$ and $p > k$, so $p$ divides $L$ exactly once and the multiples of $p$ up to $N$ are precisely $p, 2p, \ldots, kp$. Reduce the $m + 1$ integers $0, Lu_1, \ldots, Lu_m$ modulo $p$ and divide by the invertible unit $L/p \bmod p$: every denominator coprime to $p$ vanishes, while each chosen multiple $ip$ ($1 \le i \le k$) contributes $1/i \bmod p$. Thus all $m + 1$ normalized residues come from the reductions modulo $p$ of $E_k$, occupying at most $s_k$ distinct residue classes (including $0$).

   Therefore at least $v(s_k, m + 1)$ pairs among $0, Lu_1, \ldots, Lu_m$ are congruent modulo $p$, so $p^{v(s_k, m + 1)} \mid V$. Multiplying over all primes in $(N/(k+1), N/k]$ and all finitely many relevant $k$, the prime number theorem ($\sum_{N/(k+1) < p \le N/k} \log p = \frac{N}{k(k+1)} + o(N)$) gives
   $$
   \log V \ge N \sum_{k \ge 1} \frac{v(s_k, m + 1)}{k(k + 1)} + o(N).
   $$

4. **Compare bounds.** Dividing the two bounds on $\log V$ by $DN$ and letting $N \to \infty$ gives (1). $\square$

---

## Consequences

### Explicit bound when $\tau \ge 4/5$

Plug $m = 6$ (so $D = \binom{7}{2} = 21$) into (1). Since $s_1 = 2$, $s_2 = 4$, and $s_3 = 8 > 7$, only $k = 1$ and $k = 2$ contribute, with $v(2, 7) = 9$ and $v(4, 7) = 3$:
$$
\tau \le 1 - \frac{1}{21}\left(\frac{9}{1 \cdot 2} + \frac{3}{2 \cdot 3}\right) + \frac{10}{3}\gamma
= 1 - \frac{5}{21} + \frac{10}{3}\gamma
= \frac{16}{21} + \frac{10}{3}\gamma.
$$
If $\tau \ge 4/5$, then $\frac{10}{3}\gamma \ge \frac{4}{5} - \frac{16}{21} = \frac{4}{105}$, which gives $\gamma \ge \frac{2}{175}$.

### General quadratic bound for $\tau > C$

For general $m \ge 2$ and any bin count $s \ge 1$, if $t = m + 1$ items are placed into $s$ bins of sizes $c_1, \ldots, c_s$ ($\sum c_r = m + 1$), then Cauchy–Schwarz gives $\sum c_r^2 \ge (m + 1)^2 / s$, so the number of equal pairs satisfies
$$
v(s, m + 1) = \frac{1}{2}\left(\sum_{r=1}^s c_r^2 - (m + 1)\right)
\ge \frac{1}{2}\left(\frac{(m + 1)^2}{s} - (m + 1)\right).
$$
Dividing by $D = m(m + 1)/2$ yields
$$
\frac{v(s, m + 1)}{D} \ge \frac{m + 1}{ms} - \frac{1}{m}.
$$
Substituting this into (1) and using the telescoping identity $\sum_{k \ge 1} \frac{1}{k(k+1)} = 1$ gives
$$
\begin{aligned}
\tau &\le 1 - \sum_{k \ge 1} \frac{1}{k(k + 1)}\left(\frac{m + 1}{m s_k} - \frac{1}{m}\right) + \frac{2(m - 1)}{3}\gamma \\
     &= \left(1 + \frac{1}{m}\right)\left(1 - \sum_{k \ge 1} \frac{1}{k(k + 1) s_k}\right) + \frac{2(m - 1)}{3}\gamma \\
     &= C + \frac{C}{m} + \frac{2(m - 1)}{3}\gamma.
\end{aligned}
$$
Now suppose $\tau > C$, and choose $m = \lceil 2C / (\tau - C) \rceil$. Because $s_1 = 2$ and $\sum_{k \ge 1} 1/(k(k+1)s_k) \le 1/2$, we have $C \ge 1/2$ while $\tau \le 1$, so $2C / (\tau - C) \ge 2$ and $m \ge 2$ is valid. By choice of $m$, we have $C/m \le (\tau - C)/2$ and $m - 1 < 2C / (\tau - C)$, giving
$$
\frac{\tau - C}{2} \le \frac{2(m - 1)}{3}\gamma < \frac{4C}{3(\tau - C)}\gamma
\implies \gamma \ge \frac{3(\tau - C)^2}{8C}.
$$

### Numerical value of $C$

Enumerating distinct rational subset sums of $\{1, 1/2, \ldots, 1/k\}$ up to $k = 8$ gives
$$
(s_1, s_2, s_3, s_4, s_5, s_6, s_7, s_8) = (2, 4, 8, 16, 32, 52, 104, 208).
$$
Bounding the positive tail $\sum_{k \ge 9} \frac{1}{k(k+1)s_k}$ by $\frac{1}{s_8} \sum_{k \ge 9} \frac{1}{k(k+1)} = \frac{1}{9 s_8}$ brackets Sawin's constant tightly:
$$
0.6925 < C < 0.6931.
$$
This inequality rules out high rates without big jumps, while leaving open whether $-\log \delta(n)/n$ has a positive limit below $C$. [Original problem](https://www.erdosproblems.com/311)
