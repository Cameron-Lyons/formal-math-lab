# The largest complete grid near 1

Instead of hunting for a single lucky unit-fraction sum close to $1$, ask a more uniform question: *for which denominators $D$ can we represent **every** grid point $s/D$ in the interval $[1/2, 3/2]$ using distinct reciprocals from $1, 1/2, \ldots, 1/N$?*

Call such an integer $D \ge 1$ **admissible**. Remarkably, the admissible denominators are not a messy collection of unrelated integers—for all sufficiently large $N$, there is a single **divisor-maximal denominator** $D_*$ such that $D$ is admissible if and only if $D \mid D_*$. Even better, we can pin down the size of $\log D_*$ to within a tiny power of $\log\log\log N$.

## Main result

Write $L = \operatorname{lcm}(1, \ldots, N)$, and for each prime $p \le N$ let $C_p \subseteq \mathbb{F}_p$ be the set of allowable numerator residues modulo $p$ from the [prime residue criterion](prime-residues.md). For all sufficiently large $N$, define
$$
D_* = \frac{L}{\prod_{\substack{p \le N \\ C_p \ne \mathbb{F}_p}} p}.
$$
Let $L_j$ denote the $j$th iterated natural logarithm evaluated at $N$ (so $L_1 = \log N$, $L_2 = \log\log N$, $L_3 = \log\log\log N$).

**Theorem.** For all sufficiently large $N$:
1. An integer $D \ge 1$ is admissible **if and only if $D \mid D_*$**.
2. The size of $D_*$ satisfies
   $$
   \frac{N}{L_1 L_2 L_3^2} \ll \log D_* \ll \frac{N L_3}{L_1 L_2}.
   $$
   In particular, $\log D_* = N / \bigl(L_1 L_2^{1+o(1)}\bigr)$, leaving a gap of order at most $L_3^3$ between the lower and upper bounds. (Using the [variable-depth grid construction](iterated-grid.md) narrows the lower bound further to $N/B(N)$.)

---

## Exact maximality

**The big idea.** Writing a grid point $s/D$ relative to $1$ as $1 + h/L$ gives $h = (s - D)(L/D)$. For a prime $p \le N$:
* If $p \mid L/D$, then $h \equiv 0 \pmod p$ automatically—which is always allowed since $0 \in C_p$.
* If $p \nmid L/D$, then as $s$ sweeps across $[D/2, 3D/2]$, $h \bmod p$ sweeps through *all* residues modulo $p$, which succeeds if and only if $C_p = \mathbb{F}_p$.

Let us check both directions carefully.

* **Sufficiency ($D \mid D_* \implies D$ is admissible).** First take $D = D_*$. For any integer $s$ with $s/D_* \in [1/2, 3/2]$, write $s/D_* = 1 + h/L$, where $h = (s - D_*)(L/D_*)$ satisfies $|h| \le L/2$. By definition of $D_*$, every prime $p$ with $C_p \ne \mathbb{F}_p$ divides $L/D_*$, hence divides $h$; since $0 \in C_p$ always, those tests pass. At all other primes $C_p = \mathbb{F}_p$, so every residue passes automatically. By the [prime residue criterion](prime-residues.md), $s/D_* \in E_N$. For any divisor $D \mid D_*$, the grid of $D$ is a subset of the grid of $D_*$, so $D$ is admissible as well.

* **Necessity ($D$ admissible $\implies D \mid D_*$).** The case $D = 1$ is immediate. Suppose $D \ge 2$ is admissible. Its grid point $(D - 1)/D \in [1/2, 3/2]$ is in lowest terms and belongs to $E_N$, so its denominator $D$ must divide $L$. Now fix any prime $p \le N$ with $p \nmid L/D$. Since $p \mid L$, this implies $p \mid D$ (and in fact $p$ divides $D$ to the full power in $L$). As $s$ runs through the integers in $[D/2, 3D/2]$, there are at least $D \ge p$ consecutive choices of $s$; because $L/D$ is invertible modulo $p$, the offsets $h = (s - D)(L/D)$ hit every residue class modulo $p$. Necessity in the prime residue criterion forces $C_p = \mathbb{F}_p$. Equivalently, every prime with $C_p \ne \mathbb{F}_p$ divides $L/D$, which means $D \mid D_*$. $\square$

---

## Size of the largest grid

### Lower bound

The [four-stage construction](README.md#four-applications) produces a denominator $D_4$ with $\log D_4 \gg N/(L_1 L_2 L_3^2)$ such that every $s/D_4 \in [1/2, 1]$ belongs to $E_N$. Although this covers only $[1/2, 1]$ instead of $[1/2, 3/2]$, we have $D_4/N \to \infty$, so for sufficiently large $N$ the interval $[D_4/2, D_4]$ still contains at least $N \ge p$ consecutive integers for every prime $p \le N$. The necessity argument above therefore still applies and proves $D_4 \mid D_*$, giving $\log D_* \ge \log D_4 \gg N/(L_1 L_2 L_3^2)$.

### Upper bound

**Proof strategy.** To bound $D_*$ from above, we need to show that every sufficiently large prime $p \le N$ fails to cover all of $\mathbb{F}_p$ (so $C_p \ne \mathbb{F}_p$, meaning $p$ drops out of $D_*$). For $p > \sqrt{N}$, $C_p$ is simply the modulo-$p$ reduction of $E_{k_p}$ (scaled by $L/p$), where $k_p = \lfloor N/p \rfloor$. Thus $|C_p| \le |E_{k_p}|$. A naive subset count gives $|E_k| \le 2^k$, which only kills primes above $c N / \log N$ (as in [the basic obstruction](README.md#why-a-grid-cannot-give-the-conjectured-rate)). By counting *distinct* sums in $E_k$ more carefully, we save an extra $\log k / \log\log k$ factor and kill every prime above $C N L_3 / (L_1 L_2)$.

**Step 1: Elementary bound on the number of distinct sums $|E_k|$.** Let $E_k$ be the set of distinct reciprocal subset sums using denominators at most $k$. We prove that for large $k$,
$$
\log |E_k| \ll \frac{k \log\log k}{\log k}.
$$
Set $y = k / \log k$ and $Q = \operatorname{lcm}(1, \ldots, \lfloor y \rfloor)$, and split the denominators $\{1, \ldots, k\}$ into two camps:
* *Smooth denominators ($n \mid Q$):* Any subset sum of smooth denominators is a multiple of $1/Q$ lying in $[0, 1 + \log k]$, so they produce at most $1 + Q(1 + \log k)$ distinct values. By the prime number theorem, $\log Q \sim y = k/\log k$, so the logarithm of this count is $O(k / \log k)$.
* *Rough denominators ($n \nmid Q$):* Every remaining integer $n \le k$ is divisible by some prime power $q \in (y, k]$. The number of such integers $n$ is at most
  $$
  k \sum_{y < p \le k} \frac{1}{p} + k \sum_{\substack{y < p^a \le k \\ a \ge 2}} \frac{1}{p^a}.
  $$
  Cover $(y, k]$ by $O(\log\log k)$ dyadic intervals. On each dyadic interval $(w, 2w]$, $\pi(2w) \ll w/\log w$ and $\log w \asymp \log k$, so each interval contributes $O(1/\log k)$ to $\sum 1/p$. Meanwhile, there are $O(\sqrt{k} \log k)$ higher prime powers ($a \ge 2$) up to $k$, each contributing at most $1/y$ to the second sum. Hence there are at most $O(k \log\log k / \log k)$ rough denominators altogether.

Each rough denominator can be either included or excluded ($2$ choices), so multiplying the smooth value count by $2^{O(k \log\log k / \log k)}$ gives $\log |E_k| \ll k \log\log k / \log k$.

**Step 2: Eliminating all primes above $T$.** Put
$$
T = \frac{C N L_3}{L_1 L_2},
$$
where $C$ is a sufficiently large absolute constant. For any prime $p$ with $T < p \le N$, we have $p > \sqrt{N}$ (for large $N$), so $q_p = p$ and
$$
k_p = \left\lfloor \frac{N}{p} \right\rfloor \le K := \left\lfloor \frac{L_1 L_2}{C L_3} \right\rfloor.
$$
Since $C_p$ is obtained by reducing $E_{k_p}$ modulo $p$ and multiplying by the unit $L/p$, monotonicity and Step 1 give
$$
\log |C_p| \le \log |E_K| \ll K \frac{\log\log K}{\log K} \le \frac{O(1)}{C} \log N.
$$
Here we used $\log K \sim L_2$ and $\log\log K \sim L_3$ for fixed $C$. Since $\log p > \log T \sim \log N$, choosing $C$ large enough guarantees $\log |C_p| < \log p$, i.e., $|C_p| < p$, for every prime $p > T$.

**Step 3: Bounding $\log D_*$.** Every prime $p > T$ has $C_p \ne \mathbb{F}_p$ and appears in $L$ to exponent $1$, so it cancels completely out of $D_*$. The only prime powers that can survive in $D_*$ are:
* primes $p \le T$ to the first power, contributing at most $\sum_{p \le T} \log p = O(T)$ by Chebyshev's bound / the prime number theorem; and
* higher powers of primes $p \le \sqrt{N}$, contributing at most $O(\sqrt{N} \log N)$ in total since each prime power in $L$ is at most $N$.

Combining these bounds gives $\log D_* \ll T = C N L_3 / (L_1 L_2)$, completing the proof. $\square$

---

In particular, the best complete grid near $1$ guarantees an error $1/D_*$ at $1$, with $\log D_* = N / (L_1 L_2^{1+o(1)})$. An isolated sum from a non-grid residue class can still land far closer to $1$; estimating how much closer is the remaining challenge in Erdős Problem #311.
