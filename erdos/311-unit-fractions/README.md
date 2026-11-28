# Approximating 1 by sums of distinct unit fractions

Pick a cutoff $N$ and form sums of **distinct unit fractions** (reciprocals $1/n$ with $1 \le n \le N$). It is easy to hit $1$ on the nose—for example, $1/2 + 1/3 + 1/6 = 1$—so Erdős and Graham asked a subtler question: *how close to $1$ can you get without hitting $1$ exactly?*

Formally, let $E_N$ be the set of all subset sums $\sum_{n \in A} 1/n$ over subsets $A \subseteq \{1, \ldots, N\}$ (including the empty sum $0$), and define the closest nonzero miss
$$
\delta(N) = \min_{\substack{u \in E_N \\ u \ne 1}} |1 - u|.
$$
Every sum in $E_N$ has denominator dividing $L_N = \operatorname{lcm}(1, \ldots, N)$, and the prime number theorem gives $\log L_N = N + o(N)$, so $\delta(N) \ge 1/L_N = e^{-(1+o(1))N}$ automatically. On the other hand, summing powers of two ($1/2 + 1/4 + \cdots + 1/2^k = 1 - 2^{-k}$) only gets within $\approx 1/N$ of $1$. **Erdős Problem #311** asks whether $-\log \delta(N)/N$ tends to a constant $c \in (0, 1)$—that is, whether $\delta(N)$ decays exponentially at a well-defined rate strictly between $0$ and $1$. [Problem #311](https://www.erdosproblems.com/311)

This folder collects structural theorems, unconditional bounds, density results, and certified exact computations on $\delta(N)$ and on the closely related problem of filling complete evenly spaced grids near $1$.

---

## Summary of results

### Individual gap $\delta(N)$

| Topic | Main result | Details |
|---|---|---|
| **Prime-by-prime congruences** | For all sufficiently large $N$, one explicit modular congruence per prime $p \le N$ determines *exactly* which fractions in $[1/2, 3/2]$ belong to $E_N$. Thus $L\delta(N)$ is the smallest nonzero $\lvert h\rvert$ passing all prime tests, where $L = \operatorname{lcm}(1, \ldots, N)$. Estimating this least $\lvert h\rvert$ on the exponential scale remains open. | [Congruences and proof](prime-residues.md) |
| **Unconditional upper bound on $\liminf$** | Comparing three record errors gives $\liminf_{N \to \infty} (-\log \delta(N))/N \le 190/(73 + \sqrt{25849}) = 0.81274298\ldots$, and extending to four record errors with weighted linear forms sharpens this to $< 0.812741$ (root of $46 r^3 + 169 r^2 - 26 r - 225 = 0$), without assuming a limiting rate exists. | [Three-record bound](record-gaps.md) · [Four-record bound](four-records.md) · [Verifier](verify_four_records.py) |
| **Change indices and constant runs** | Only $\sim X \log\log X / \log X$ integers up to $X$ alter the attainable sums $E_n \cap [3/4, 5/4]$, and every short interval $[Y, Y + Y^\eta]$ contains a block of length $\gg_\eta \log Y / \log\log\log Y$ on which $\delta(n)$ is constant. | [Change indices](change-indices.md) · [Constant intervals](constant-intervals.md) |
| **Jump sizes and reduced heights** | Any peak rate $\limsup (-\log \delta(n))/n$ above Sawin's constant $C \approx 0.693$ forces macroscopic single-step jumps $\log(\delta(n-1)/\delta(n)) \gg n$, while improvements with subexponential reduced numerator and denominator contribute only $o(X)$ to $-\log \delta(X)$. | [Peak jumps](peak-jumps.md) · [Jump heights](jump-heights.md) |
| **Near-saturation density** | For any $g(N) = o(N)$, indices with $L\delta(N) \le e^{g(N)}$ have natural density $0$. An exact modular sieve also certifies $L\delta(N) > N^5$ for all $1{,}000 \le N \le 1{,}000{,}000$. | [Density proof and finite certificate](near-saturation.md) |
| **Certified exact values ($58 \le N \le 200$)** | The exact minimum $\delta(N)$ is certified for every $58 \le N \le 200$, with both an explicit witness subset and an independent exclusion of smaller nonzero gaps, agreeing with the earlier table through $60$ on the overlap. | [Method and verification](exact-values.md) · [Exact values and witnesses](exact_gaps.tsv) |

### Complete grids near 1 vs. individual gaps

A central theme across these notes is the sharp separation between two tasks:

* **Complete grids:** representing *every* fraction $s/D$ near $1$ with a fixed common denominator $D$.
* **Individual gaps:** finding just *one* lucky fraction in $E_N \setminus \{1\}$ close to $1$.

Complete grids are much easier to construct explicitly, and their maximum resolution is now pinned down up to iterated-logarithm factors—but as shown below, complete grids can never achieve a positive exponential rate $\log D \gg N$:

* **Largest complete grid & symmetric gap:** The prime congruences pinpoint a single divisor-maximal denominator $D_*$ such that every $s/D \in [1/2, 3/2]$ is representable if and only if $D \mid D_*$. Its size satisfies $\log D_* = N / (\log N \, (\log\log N)^{1+o(1)})$. The exact same scale governs $-\log \delta_{\rm sym}(N)$, where $\delta_{\rm sym}(N)$ is the smallest $e > 0$ such that *both* $1 - e$ and $1 + e$ lie in $E_N$; in particular, the symmetric variant has exponential rate $0$. [Maximal grid denominator](largest-grid.md) · [Symmetric-gap proof](symmetric-gaps.md)
* **Variable-depth iterated grid:** Let $B(N)$ be the product of all successive iterated logarithms of $N$ that are at least $2$. Iterating prime extensions across a growing number of logarithmic stages constructs a complete grid on $[1/2, 3/2]$ with $\log D \ge aN/B(N)$, giving $\delta(N) \le \exp(-aN/B(N))$ for an absolute constant $a > 0$ and all sufficiently large $N$. [Variable-depth construction](iterated-grid.md)

The remainder of this page walks through a clean self-contained **four-stage grid construction**, explains why *no* complete grid can resolve the conjectured exponential rate in #311, and proves an **exact reduction** showing how #311 collapses to a single residue-distance problem on the large prime powers.

---

## A self-contained four-stage grid bound

Write $L_1(x) = \log x$ and $L_{j+1}(x) = \log L_j(x)$ for the iterated natural logarithms.

**Theorem (Four-stage bound).** There is an absolute constant $b > 0$ such that for every sufficiently large $N$, there is a common denominator $D$ with
$$
\log D \ge \frac{bN}{L_1(N) L_2(N) L_3(N)^2}
$$
such that $s/D \in E_N$ for **every integer** $s$ between $D/2$ and $D$. In particular, taking $s = D - 1$ gives an approximation from below with
$$
\delta(N) \le \exp\!\left(-\frac{bN}{L_1(N) L_2(N) L_3(N)^2}\right).
$$

Because $L_1(N) L_2(N) L_3(N)^2 \to \infty$, this construction yields no positive lower bound on $-\log \delta(N)/N$ independent of $N$; rather, it pushes the guaranteed subexponential decay as close to $\exp(-cN/\log N)$ as four elementary stages allow.

## How to add primes to a common denominator

**The big idea.** Suppose you already know how to build every fraction $m/D$ in an interval $[a, 1]$ using distinct divisors of $D$ bounded by $B$. To multiply the grid resolution $D$ by a fresh product of primes $P = \prod_{p \in \mathcal{P}} p$, you peel off each new prime $p \in \mathcal{P}$ one residue at a time using the Chinese remainder theorem: choose a numerator $m_p \in [aD, D]$ that matches your target numerator $s \bmod p$, represent $m_p/D$ on the old grid, and scale all of its denominators by $p$. After subtracting all those scaled pieces, what remains is a fraction $m/D$ back on the old grid! Because each scaled piece uses *only* its own new prime $p$ and no other prime from $\mathcal{P}$, the denominator groups cannot collide.

Let us make this precise. Suppose $0 \le a < 1$, and suppose every integer $m$ with $aD \le m \le D$ has a representation of $m/D$ as a sum of distinct unit fractions whose denominators divide $D$ and are at most $B$. Let $\mathcal{P}$ be a finite nonempty set of primes coprime to $D$, put $P = \prod_{p \in \mathcal{P}} p$, and suppose $[aD, D]$ contains at least $p$ integers for every $p \in \mathcal{P}$.

**Lemma.** Every fraction $s/(DP)$ with $s \in \mathbb{Z}$ and
$$
a + \sum_{p \in \mathcal{P}} \frac{1}{p} \le \frac{s}{DP} \le 1
$$
has a representation as a sum of distinct unit fractions whose denominators divide $DP$ and are at most $B \max \mathcal{P}$.

*Quick sanity check.* Take $D = 4$, $a = 0$, $B = 4$ (binary fractions using $\{1, 2, 4\}$ cover every $m/4 \in [0, 1]$), and add $\mathcal{P} = \{3\}$, so $P = 3$ and $[0, 4]$ has $5 \ge 3$ integers. To build $11/12$ ($s = 11$): solve $m_3 \cdot 1 \equiv 11 \equiv 2 \pmod 3$ in $[0, 4]$ to get $m_3 = 2$. Then $m = (11 - 2)/3 = 3 \in [0, 4]$. Representing $m/4 = 3/4 = 1/2 + 1/4$ (no factor of $3$) and scaling $m_3/4 = 2/4 = 1/2$ by $3$ to get $1/6$ (divisible by $3$) yields $1/2 + 1/4 + 1/6 = 11/12$, with disjoint denominators dividing $12$ and at most $4 \cdot 3 = 12$.

**Proof of the Lemma.**
1. **Match each prime residue.** For each $p \in \mathcal{P}$, choose an integer $m_p \in [aD, D]$ satisfying
   $$
   m_p (P/p) \equiv s \pmod p.
   $$
   This is always possible: $P/p$ is invertible modulo $p$ because $P$ is squarefree, and $[aD, D]$ contains at least $p$ consecutive integers, so it hits every residue class modulo $p$.
2. **Peel off the $P$-part.** Define
   $$
   m = \frac{s - \sum_{p \in \mathcal{P}} m_p (P/p)}{P}.
   $$
   For every $p \in \mathcal{P}$, every term $m_q (P/q)$ with $q \ne p$ is divisible by $p$, so the numerator is congruent to $s - m_p (P/p) \equiv 0 \pmod p$. Because $P$ is a product of distinct primes, $P$ divides the numerator and $m$ is an integer.
3. **Check that $m/D$ lands back in $[a, 1]$.** Dividing by $D$ gives
   $$
   \frac{m}{D} = \frac{s}{DP} - \sum_{p \in \mathcal{P}} \frac{m_p}{pD}.
   $$
   Since $0 \le aD \le m_p \le D$, each subtracted term $m_p/(pD)$ lies in $[0, 1/p]$. Combining this with the hypothesis $a + \sum_{p \in \mathcal{P}} 1/p \le s/(DP) \le 1$ guarantees $m/D \in [a, 1]$.
4. **Assemble disjoint unit-fraction groups.** Represent $m/D$ using the given denominators dividing $D$ and bounded by $B$. For each $p \in \mathcal{P}$, represent $m_p/D$ in the same way and multiply every denominator in that representation by $p$. Adding the unscaled representation and all scaled representations gives $m/D + \sum_{p \in \mathcal{P}} m_p/(pD) = s/(DP)$.
   * Every denominator in the $p$-group is divisible by $p$ and by no other prime in $\mathcal{P}$ (since old denominators divide $D$, which is coprime to $P$).
   * Every denominator in the unscaled group is divisible by none of the primes in $\mathcal{P}$.

   Hence all groups are pairwise disjoint, every denominator divides $DP$, and the largest denominator used is at most $B \max \mathcal{P}$. $\square$

## Four applications

**Proof strategy.** Each application of the lemma multiplies the common denominator $D$ by a huge prime product $P$ (giving $\log D' \gtrsim x$), while multiplying the largest *used* denominator by only $\max \mathcal{P} \le x$. The trick is that the lemma only needs the *previous* denominator $D_{\mathrm{old}}$ to be at least $O(x)$—not $e^x$! Because $D_{\mathrm{old}}$ is already exponential in its own scale $y$, we can feed in an exponentially smaller scale $y = 6 \log x$ at each stage, collapsing the maximum denominator from $O(x^2)$ down to $O(x L_1(x) L_2(x) L_3(x)^2)$.

For a large real number $x$, take $\mathcal{P}$ to be all primes in the dyadic interval $(x/2, x]$, with product $P$. The prime number theorem gives $\log P \sim x/2$, and $\sum_{x/2 < p \le x} 1/p \le 2\pi(x)/x = o(1)$. All we need is that for sufficiently large $x$,
$$
\log P \ge \frac{x}{3} \qquad \text{and} \qquad \sum_{x/2 < p \le x} \frac{1}{p} \le \frac{1}{8}.
$$

1. **Stage 1 (binary base + one prime block).** Start with the least power of two $D_0 \ge 2x + 2$. Ordinary binary expansion represents every $m/D_0 \in [0, 1]$ using distinct denominators from $\{1, 2, 4, \ldots, D_0\}$. Since $[0, D_0]$ contains more than $x$ integers and all primes in $(x/2, x]$ are odd (hence coprime to $D_0$), the lemma produces a denominator $D_1(x) = D_0 P$ covering $[1/8, 1]$. Its largest prime factor is at most $x$, its size satisfies $\log D_1(x) \ge x/3$, and the unit-fraction denominators used are bounded by
   $$
   H_1(x) \le x D_0 = O(x^2).
   $$
2. **Stages 2, 3, and 4 (exponential scale reduction).** To pass from stage $j$ to stage $j+1$ for $j = 1, 2, 3$, evaluate the stage-$j$ construction at the much smaller scale $y = 6 \log x$.
   * Its common denominator satisfies $D_j(y) \ge e^{y/3} = x^2$.
   * All of its prime factors are at most $y < x/2$, so $D_j(y)$ is coprime to every prime in $(x/2, x]$.
   * Because $j \le 3$, the covered interval $[(j/8) D_j(y), D_j(y)]$ has length at least $\frac{5}{8} x^2 > x$, so it contains at least $x$ integers.

   Applying the lemma with the primes in $(x/2, x]$ yields a new denominator $D_{j+1}(x) = D_j(y) P$ covering $[(j+1)/8, 1]$, with all prime factors at most $x$ and $\log D_{j+1}(x) \ge x/3$. The largest unit-fraction denominator satisfies the recurrence
   $$
   H_{j+1}(x) \le x H_j(6 \log x).
   $$

Unrolling this recurrence starting from $H_1(t) = O(t^2)$ gives:
$$
\begin{aligned}
H_2(x) &\ll x L_1(x)^2, \\
H_3(x) &\ll x L_1(x) L_2(x)^2, \\
H_4(x) &\ll x L_1(x) L_2(x) L_3(x)^2.
\end{aligned}
$$
Finally, choose $x = c N / (L_1(N) L_2(N) L_3(N)^2)$ for a sufficiently small fixed constant $c > 0$. Then $H_4(x) \le N$ for all sufficiently large $N$, the covered interval is $[4/8, 1] = [1/2, 1]$, and $\log D_4(x) \ge x/3$. Setting $b = c/3$ proves the four-stage bound.

---

## Why a grid cannot give the conjectured rate

Why can't we push the grid construction further to reach $\log D \gg N$ and solve Erdős Problem #311? Because there is an elementary information-theoretic barrier: **requiring every numerator $s/D \in [1/2, 1]$ to occur forces $\log D = O(N / \log N)$**, even if we allow denominators in $E_N$ that do not divide $D$.

**Proof.** We may assume $D > 2N + 2$. Since $(D - 1)/D \in E_N$ is already in lowest terms, its denominator $D$ must divide $\operatorname{lcm}(1, \ldots, N)$.

Now fix any prime $p \mid D$ with $p > \sqrt{N}$. Because $p^2 > N$, both $D$ and every multiple $pk \le N$ contain only a *single* factor of $p$. Take a representation of $s/D \in E_N$, multiply both sides by $p$, and reduce modulo $p$:
* On the right-hand side, every denominator coprime to $p$ vanishes modulo $p$, while each selected multiple $pk \le N$ contributes $1/k \bmod p$. There are at most $\lfloor N/p \rfloor$ such multiples, so the right-hand side can attain at most $2^{\lfloor N/p \rfloor}$ residues modulo $p$.
* On the left-hand side, $p \cdot (s/D) = s \cdot (D/p)^{-1} \bmod p$. Because $D/p$ is invertible modulo $p$ and $s$ runs through at least $D/2 > N \ge p$ consecutive integers in $[D/2, D]$, the left-hand side attains **all $p$ residues** modulo $p$.

Comparing the counts yields
$$
p \le 2^{\lfloor N/p \rfloor}, \qquad \text{so} \qquad p \log p \le N \log 2.
$$
In particular, $p \le 2 (\log 2) N / \log N$. By the prime number theorem, the product of all primes up to $2(\log 2) N/\log N$ has logarithm $O(N/\log N)$. Meanwhile, primes $p \le \sqrt{N}$ each appear in $D$ to a power at most $N$, so they contribute at most $\sqrt{N} \log N$ altogether to $\log D$.

Hence $\log D = O(N/\log N)$ (and [the maximal-grid analysis](largest-grid.md) sharpens this to $\log D_* = N / (\log N \, (\log\log N)^{1+o(1)})$). An isolated fraction in $E_N$ can still land exponentially closer to $1$ than any complete grid allows—its neighbors simply need not be representable. Pinning down the size of that individual gap is the true unknown in #311.

---

## An exact reduction for the target 1

Although complete grids cannot reach $\exp(-cN)$ by themselves, a slightly smaller complete grid lets us strip away all "smooth" denominators and isolate the exact heart of Problem #311.

**The big idea.** Choose a smooth threshold $S$ just below $N/\text{polylog}(N)$ and set $Q = \operatorname{lcm}(1, \ldots, \lfloor S \rfloor)$. Every denominator up to $N$ falls into one of two disjoint camps:
1. **Smooth denominators** (divisors of $Q$): these are rich enough to build a *complete* grid $m/Q$ covering the entire interval $[1/3, 1]$.
2. **Rough denominators** ($U = \{1 \le n \le N : n \nmid Q\}$): these are so sparse that their total reciprocal sum $R(U) = \sum_{n \in U} 1/n$ is $o(1)$!

Whenever we choose a rough subset $B \subseteq U$ with reciprocal sum $R(B) = \sum_{n \in B} 1/n$, we only need the smooth camp to approximate $1 - R(B)$ by a grid point $m/Q$ (without hitting $1 - R(B)$ exactly). Since $1 - R(B)$ sits comfortably inside $[1/3, 1]$, the best possible smooth match is *always* attainable!

Formally, let $S = c N / (L_1(N)^3 L_2(N)^4)$ for a sufficiently small constant $c > 0$, and put $Q = \operatorname{lcm}(1, \ldots, \lfloor S \rfloor)$. Every fraction $m/Q \in [1/3, 1]$ can be represented using distinct divisors of $Q$ at most $N$; this follows from the proof of Liu and Sawhney's Lemma 4.1, and our prime-by-prime analysis also gives a self-contained elementary proof using the first grid construction. [Liu and Sawhney, Proposition 3.2 and Lemma 4.1](https://arxiv.org/html/2404.07113v1#S4) · [Elementary derivation](prime-residues.md)

Set $U = \{n \le N : n \nmid Q\}$ (with $n$ positive) and $R(B) = \sum_{n \in B} 1/n$. For real $z$, define the **nonzero distance to the nearest integer**
$$
d_*(z) = \min_{\substack{k \in \mathbb{Z} \\ k \ne z}} |z - k|,
$$
so $d_*(z) = 1$ whenever $z \in \mathbb{Z}$.

**Proposition (Exact reduction).** For all sufficiently large $N$,
$$
\delta(N) = \frac{1}{Q} \min_{B \subseteq U} d_*\bigl(Q R(B)\bigr).
$$
More generally, the exact same right-hand side equals the minimum nonzero distance from $E_N$ to **any fixed rational $t \in (1/3, 1]$**, once $N$ is sufficiently large in terms of $t$.

**Proof.**
1. **Rough denominators have tiny total sum ($R(U) = o(1)$).** Every $n \in U$ is divisible by at least one prime power $q > S$ (with $q \le N$). For a fixed $q$, the multiples of $q$ up to $N$ have reciprocal sum at most $(1 + \log(N/S))/q$.
   * Splitting the primes $q \in (S, N]$ into dyadic intervals and applying $\pi(x) \ll x/\log x$ bounds their reciprocal sum by $O((1 + \log(N/S)) / \log S)$.
   * There are $O(\sqrt{N} \log N)$ higher prime powers ($q = p^a$, $a \ge 2$) up to $N$, each contributing at most $1/S$ to $\sum 1/q$.

   Since $N/S$ is polylogarithmic in $N$, both parts vanish as $N \to \infty$, giving $R(U) = o(1)$. Also $Q/N \to \infty$ by the prime number theorem.
2. **Matching any target $t \in (1/3, 1]$.** For large $N$, the fixed denominator of $t$ divides $Q$, so $Qt \in \mathbb{Z}$. Given any rough subset $B \subseteq U$, any complementary smooth sum using divisors of $Q$ is an integer multiple $m/Q$, so its nonzero distance to $t - R(B)$ is at least
   $$
   \frac{1}{Q} d_*\bigl(Q(t - R(B))\bigr) = \frac{1}{Q} d_*\bigl(Q R(B)\bigr)
   $$
   because $Qt$ is an integer.
3. **Attainability.** This lower bound is always achieved:
   * If $B \ne \emptyset$, then $1/N \le R(B) \le R(U) = o(1)$ uniformly, so for large $N$ the shifted target $t - R(B)$ lies strictly inside $[1/3, 1]$ at distance at least $1/Q$ from both endpoints. Therefore a nearest grid point $m/Q \ne t - R(B)$ lies inside $[1/3, 1]$, can be represented by Liu and Sawhney's lemma using divisors of $Q$, and is automatically disjoint from $B \subseteq U$.
   * If $B = \emptyset$, use the grid point $t - 1/Q \in [1/3, 1]$, which achieves $d_*(0)/Q = 1/Q$.

   Taking the minimum over all $B \subseteq U$ yields the formula. $\square$

Because $\log Q \sim S = o(N)$, deciding whether $-\log \delta(N)/N$ has a positive limit in #311 is completely equivalent to deciding it for the least nonzero distance $\min_{B \subseteq U} d_*(Q R(B))$ in this residue problem. Note that simply counting how many distinct residues $Q R(B) \bmod 1$ exist does not by itself tell us how close one of them must land to an integer. [Sawin's discussion of counting distinct sums](https://www.erdosproblems.com/forum/thread/311)

---

## Numerical replay and prior work

The Python 3.10+ verifier checks the prime-adding construction by exact rational arithmetic. On the first application it verifies every numerator from $472$ through $840$ for $D = 560$; after a second application it verifies both endpoints, $1$, and the symmetric pair $1 \pm 1/373520$. [Verifier](verify_grid.py) · [Extension through $3/2$](iterated-grid.md#adding-a-prime-interval)

~~~sh
python3 erdos/311-unit-fractions/verify_grid.py
~~~

**Prior work and priority note.** Tang's January 2026 note gives $\delta(N) \le \exp(-cN / [(\log N)^3 (\log\log N)^3])$; the four-stage bound above (and the [variable-depth construction](iterated-grid.md)) gives a larger guaranteed exponent. Related constructions in the literature include Bleicher and Erdős's interval of divisor sums, Liu and Sawhney's representation of all numerators in an interval for smooth denominators, and Chen's covering of residues at almost all primes. These results address closely related questions, and priority for the bound above has not been established. [Tang, Theorem 4.1](https://github.com/QuanyuTang/erdos-problem-311-note) · [Bleicher and Erdős, Lemma 4](https://users.renyi.hu/~p_erdos/1976-10.pdf) · [Liu and Sawhney, Lemma 4.1](https://arxiv.org/html/2404.07113v1#S4) · [Chen, Lemma 13](https://hexagonmath.org/pdf/2611.01130v1)
