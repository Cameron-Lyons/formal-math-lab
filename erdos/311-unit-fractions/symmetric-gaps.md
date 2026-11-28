# Symmetric gaps around 1

Erdős Problem #311 asks how close to $1$ you can get from *at least one side* using distinct unit fractions $1/n$ ($n \le N$). What happens if we ask for a **symmetric** approximation—an error $e > 0$ such that *both* $1 - e$ and $1 + e$ are attainable?

Let $E_N$ be the set of sums of distinct reciprocals with denominators in $\{1, \ldots, N\}$, and define the **symmetric gap**
$$
\delta_{\rm sym}(N) = \min\bigl\{e > 0 : 1 - e \in E_N \text{ and } 1 + e \in E_N\bigr\}.
$$
(For $N \ge 2$, the pair $1/2$ and $3/2 = 1 + 1/2$ already shows $\delta_{\rm sym}(N) \le 1/2$.)

Unlike the one-sided gap $\delta(N)$, the symmetric gap is completely understood on the exponential scale: **its exponential rate is zero**, and in fact $-\log \delta_{\rm sym}(N)$ has the exact same order of magnitude $N / (\log N \, (\log\log N)^{1+o(1)})$ as the [largest complete grid](largest-grid.md). Even more strikingly, if you take a *single* fraction $t \in E_N$ whose reduced denominator is exponentially large (as any strong solution to #311 must have), you must expand the cutoff $N$ by a factor of $\log N \, (\log\log N)^{1+o(1)}$ before its reflection $2 - t$ becomes attainable!

---

## Why the exponential rate is zero

**The big idea.** Add the representations of $1 - e$ and $1 + e$ together! The unknown error $e$ cancels out completely, leaving an exact representation of $2$ with multiplicities in $\{0, 1, 2\}$. A classic divisibility trick (clearing denominators and reducing modulo any participating prime $p$) then forces every prime $p$ dividing the denominators to satisfy $\log p = O(N/p)$, which kills all primes above $O(N/\log N)$.

Let us write out the proof:
1. **Cancel the error.** Adding the two representations $1 - e = \sum_{n \in A} 1/n$ and $1 + e = \sum_{n \in B} 1/n$ yields
   $$
   \sum_{n=1}^N \frac{c_n}{n} = 2, \qquad c_n \in \{0, 1, 2\}.
   $$
   Let $Q$ be the least common multiple of the denominators actually used (those with $c_n > 0$). Because $e = (1 + e) - 1$ is a positive integer multiple of $1/Q$, we have $\delta_{\rm sym}(N) \ge 1/Q$, so it suffices to bound $\log Q$.
2. **Bound the largest prime dividing $Q$.** Fix any prime $p \mid Q$, set $k = \lfloor N/p \rfloor$, and put $\Lambda_k = \operatorname{lcm}(1, \ldots, k)$. Multiply $\sum_{n=1}^N c_n/n = 2$ by $p \Lambda_k$ and separate the multiples of $p$ from the rest:
   $$
   m := \sum_{j=1}^k c_{pj} \frac{\Lambda_k}{j} = 2 p \Lambda_k - p \sum_{\substack{1 \le n \le N \\ p \nmid n}} c_n \frac{\Lambda_k}{n}.
   $$
   Every $j \le k$ divides $\Lambda_k$, and at least one multiple $pj$ has $c_{pj} \ge 1$ (since $p \mid Q$), so $m$ is a positive integer satisfying
   $$
   1 \le m \le 2 k \Lambda_k.
   $$
   Meanwhile, every term in the sum on the right-hand side has denominator coprime to $p$, so the right-hand side is $p$ times a rational number whose denominator is prime to $p$. Reducing modulo $p$ therefore gives $p \mid m$.
3. **Apply Chebyshev's bound.** Since each prime power dividing $\Lambda_k$ is at most $k$, we have $\log \Lambda_k \le \pi(k) \log k = O(k)$. Hence $\log p \le \log m = O(k) = O(N/p)$. Splitting at $p = \sqrt{N}$ shows that every participating prime satisfies $p \ll N / \log N$ (for $p \le \sqrt{N}$ this is automatic; for $p > \sqrt{N}$ we have $\log p > \frac{1}{2} \log N$, so $p \ll N/\log p \ll N/\log N$). (This is the large-prime argument of Martin's Lemma 8 adapted to multiplicities up to $2$. [Martin, *Denser Egyptian fractions*, §3](https://matwbn.icm.edu.pl/ksiazki/aa/aa95/aa9533.pdf))
4. **Sum over surviving primes.** By $\pi(x) \ll x/\log x$, there are $O(N / (\log N)^2)$ primes up to $O(N/\log N)$. Each contributes at most $\log N$ to $\log Q$ because its highest power in $Q$ divides some $n \le N$. Consequently,
   $$
   -\log \delta_{\rm sym}(N) \ll \frac{N}{\log N}, \qquad \text{and therefore} \qquad \lim_{N \to \infty} \frac{-\log \delta_{\rm sym}(N)}{N} = 0.
   $$

Erdős Problem #311 asks about a *single* approximation, where this cancellation does not happen. Already at $N = 4$, subset sums of $\{12, 6, 4, 3\}$ divided by $12$ show that the closest sum different from $1$ is $13/12 = 1/2 + 1/3 + 1/4$ (gap $1/12$), whereas $11/12$ is missing and the closest symmetric pair is $3/4, 5/4$ (gap $1/4$). [Erdős problem #311](https://www.erdosproblems.com/311)

---

## The sharper estimate

Write $\ell_j = \log_j N$ for the $j$th iterated natural logarithm, and let $B(N)$ be the product of all iterated logarithms of $N$ that are at least $2$.

**Theorem.** For all sufficiently large $N$,
$$
\frac{N}{B(N)} \ll -\log \delta_{\rm sym}(N) \ll \frac{N \ell_3}{\ell_1 \ell_2},
$$
and in particular
$$
-\log \delta_{\rm sym}(N) = \frac{N}{\ell_1 \ell_2^{1+o(1)}}.
$$

### Lower bound

The [variable-depth grid construction](iterated-grid.md) produces a denominator $D$ with $\log D \gg N/B(N)$ such that every $s/D \in [1/2, 3/2]$ belongs to $E_N$. Taking $s = D - 1$ and $s = D + 1$ realizes both $1 - 1/D$ and $1 + 1/D$, proving $-\log \delta_{\rm sym}(N) \ge \log D \gg N/B(N)$. (The same grid shows $\log D_* \gg N/B(N)$ for the [largest complete grid](largest-grid.md) denominator $D_*$.)

### Upper bound

**Proof strategy.** In the basic bound above, we treated each large prime $p$ individually via $p \le 2k\Lambda_k$. We can do much better by putting *all* primes $p > y = N/(K+1)$ into a single basket! Every such prime must divide one of the positive integers in the small set $\Lambda_K (E_K + E_K)$. Taking the product of *all* integers in that set bounds the product of all surviving primes above $y$ simultaneously.

Fix a single cutoff
$$
K = \left\lfloor \frac{\eta \ell_1 \ell_2}{\ell_3} \right\rfloor
$$
for a sufficiently small absolute constant $\eta > 0$, and put $y = N/(K+1)$.

1. **One product captures all primes above $y$.** If a prime $p > y$ divides $Q$, then $p > \sqrt{N}$ (for large $N$) and $\lfloor N/p \rfloor \le K$. By the divisibility argument above with $\Lambda_K = \operatorname{lcm}(1, \ldots, K)$, $p$ divides the positive integer
   $$
   m_p = \sum_{j=1}^K c_{pj} \frac{\Lambda_K}{j} \in \Lambda_K (E_K + E_K),
   $$
   because $c_{pj} \in \{0, 1, 2\}$ comes from adding two subset indicators on $\{1, \ldots, K\}$.
2. **Bound the product of all possible $m_p$.** The set $\Lambda_K (E_K + E_K)$ contains at most $|E_K|^2$ positive integers, each bounded by $2 K \Lambda_K$. Taking the product of all nonzero elements in this set gives a single positive integer divisible by *every* prime $p > y$ that divides $Q$. Its logarithm is at most $|E_K|^2 \log(2 K \Lambda_K) = O(K |E_K|^2)$. (Chen uses a related prime-divisor count for differences of reciprocal sums. [Chen, §9](https://hexagonmath.org/pdf/2611.01130v1))
3. **Apply the $|E_K|$ estimate.** From the [estimate for the number of distinct sums](largest-grid.md#size-of-the-largest-grid), $\log |E_K| \ll K \log\log K / \log K$. Since $\log K \sim \ell_2$ and $\log\log K \sim \ell_3$, choosing $\eta$ small enough gives $|E_K|^2 \le N^{1/2}$.
4. **Combine large and small primes.** Each prime $p > y > \sqrt{N}$ divides $Q$ only to the first power, so their combined contribution to $\log Q$ is $O(K |E_K|^2) = O(K \sqrt{N})$. The smaller primes $p \le y$ contribute at most $\pi(y) \log N = O(y)$ (since each prime power in $Q$ is at most $N$). Therefore
   $$
   \log Q \ll y + K \sqrt{N} \ll \frac{N}{K} \asymp \frac{N \ell_3}{\ell_1 \ell_2}.
   $$
Since $B(N) = \ell_1 \ell_2^{1+o(1)}$, the lower and upper bounds match at the scale $N / (\ell_1 \ell_2^{1+o(1)})$. $\square$

---

## How far must the cutoff grow to reflect a sum?

Suppose you have an attainable fraction $t \in E_N \cap [1/2, 3/2]$—for instance, a very tight one-sided approximation to $1$. Its mirror image across $1$ is $2 - t$. Define:
* $M(t) = \min\{M \ge N : 2 - t \in E_M\}$, the **reflection delay** (the smallest cutoff at which the mirror image $2 - t$ becomes attainable), and
* $R(N) = \max_{t \in E_N \cap [1/2, 3/2]} M(t)$, the worst-case reflection cutoff.

**Theorem.** For all sufficiently large $N$,
$$
R(N) = N \log N \, (\log\log N)^{1+o(1)}.
$$
Moreover, the exact same estimate holds for the individual delay $M(t)$ of **any** $t \in E_N \cap [1/2, 3/2]$ whose reduced denominator satisfies $\log \operatorname{den}(t) \ge bN$ for a fixed constant $b > 0$—in particular, whenever $0 < |1 - t| \le e^{-bN}$, since $|1 - t| \ge 1/\operatorname{den}(t)$.

### Upper bound ($R(N) \le N H$)

Run the [iterated-grid construction](iterated-grid.md) at the tiny scale $x = \log N$. It produces a denominator $G > e^{\log N + 3} > 2N$ covering $[1/2, 1]$ using distinct denominators at most $H = \lceil C B(N) \rceil$. (In particular, $(G-1)/G \in E_H$ forces $G \mid \Lambda_H$.)

We claim that $M = NH$ represents *every* fraction $u \in [1/2, 3/2]$ whose denominator divides $\Lambda_N$ (which includes $2 - t$ for every $t \in E_N \cap [1/2, 3/2]$). Write $u = 1 + h/\Lambda_M$ and check the [prime residue criterion](prime-residues.md) at each prime $p \le M$, letting $q$ be the largest power of $p$ at most $M$:
* **If $q > N$:** Because the denominator of $u$ divides $\Lambda_N$, its $p$-adic valuation is strictly smaller than that of $q$. Hence $p \mid h$, and $0$ is always an allowed residue.
* **If $q \le N$:** By maximality of $q$, $pq > M = NH$, which forces $p > H$. Since $G \mid \Lambda_H$, all prime factors of $G$ are at most $H < p$, so $p \nmid G$. Also $[G/2, G]$ contains at least $N \ge p$ consecutive integers, so the grid fractions $s/G \in [1/2, 1]$ cover *all* residues modulo $p$. Multiplying their denominators by $q$ uses denominators at most $qH \le NH = M$ and realizes every numerator residue $(\Lambda_M/q)(s/G) \bmod p$.

Every prime test passes, so $u \in E_M$ and $R(N) \le NH = O(N B(N)) = N \log N \, (\log\log N)^{1+o(1)}$.

### Lower bound and concrete examples

If $t \in E_N \cap [1/2, 3/2]$ has $\log \operatorname{den}(t) \ge bN$, then $t$ and $2 - t$ form a symmetric pair at cutoff $M = M(t)$ whose offset $e = |1 - t|$ has reduced denominator $\operatorname{den}(t)$ (which divides the LCM $Q$ of the denominators used). The sharp upper bound on $\log Q$ from the previous section gives
$$
bN \le \log \operatorname{den}(t) \ll \frac{M \log_3 M}{\log M \log_2 M}.
$$
Since $N \le M \ll N B(N)$, we have $\log M \sim \ell_1$, $\log_2 M \sim \ell_2$, and $\log_3 M \sim \ell_3$, which rearranges to $M \gg_b N \ell_1 \ell_2 / \ell_3$, matching the upper bound up to $\ell_3^{O(1)}$.

* **Simple worst-case example:** Take $t = 1 + \sum_{N/2 < p \le N} 1/p$. The sum over primes is $o(1)$ (so $t \in [1/2, 3/2]$ for large $N$), and every prime $p \in (N/2, N]$ survives in $\operatorname{den}(t)$, giving $\log \operatorname{den}(t) = (1/2 + o(1)) N$ by the prime number theorem.
* **Examples arbitrarily close to $1$ on both sides:** Even fractions within $\exp(-aN/B(N))$ of $1$ can exhibit the full reflection delay! Let $s = \sum_{N/2 < p \le N} 1/p$ and take the two grid points $g_-, g_+$ immediately bracketing $1 - s$ from the [iterated-grid construction](iterated-grid.md) at scale $x = N/(C B(N))$. For large $N$, $1/N \le s = o(1)$ and $D > N$, so both $g_-, g_+$ lie in $[1/2, 1]$, and all prime factors of $D$ are at most $2x < N/2$. Adding $s$ to $g_-$ and to $g_+$ uses disjoint denominators, preserves every prime $p \in (N/2, N]$ in the reduced denominator (so neither sum equals $1$ and both have $\log \operatorname{den} \ge (1/2 + o(1))N$), and lands within $1/D \le \exp(-aN/B(N))$ on opposite sides of $1$—yet neither can be reflected until $M = N \log N \, (\log\log N)^{1+o(1)}$.

---

## Which reduced denominators occur?

Just as the [largest complete grid](largest-grid.md) has an exact divisor-maximal denominator $D_*$, the set of all reduced denominators of symmetric gaps $e \in (0, 1/2]$ also has an exact divisor-maximal characterization!

Let $L = \Lambda_N = \operatorname{lcm}(1, \ldots, N)$. For each prime $p \le N$, let $C_p \subseteq \mathbb{F}_p$ be the allowed residue set from the [prime residue criterion](prime-residues.md), and define the **symmetric residue set**
$$
S_p = C_p \cap (-C_p).
$$
Notice that $0 \in S_p$ always, and $S_p \ne \{0\}$ means there exists at least one *nonzero* residue $r \bmod p$ such that both $r$ and $-r$ lie in $C_p$.

**Theorem.** For all sufficiently large $N$, the reduced denominators of symmetric offsets $0 < e \le 1/2$ (such that both $1 - e$ and $1 + e$ belong to $E_N$) are **precisely** the divisors $d \ge 2$ of
$$
D_{\rm sym} = \frac{L}{\prod_{\substack{p \le N \\ S_p = \{0\}}} p}.
$$

**Proof.**
* **Necessity.** By the [prime residue criterion](prime-residues.md), both $1 - h/L$ and $1 + h/L$ (with $0 < h \le L/2$) belong to $E_N$ if and only if $h \bmod p \in S_p$ for every prime $p \le N$. In particular, every prime $p$ with $S_p = \{0\}$ must divide $h$. Writing $e = h/L = r/d$ in lowest terms gives $d = L / \gcd(h, L)$, so every prime $p$ with $S_p = \{0\}$ divides $\gcd(h, L) = L/d$; equivalently, $d \mid D_{\rm sym}$.
* **Sufficiency.** Conversely, fix any divisor $d \mid D_{\rm sym}$ with $d \ge 2$, and set $b = L/d$. We construct an integer $r$ coprime to $d$ with $0 < |r| \le d/2$ such that $h = br$ passes every symmetric residue test (so $e = |h|/L = |r|/d$ has reduced denominator $d$):
  * For each prime $p \mid d$ with $p \nmid b$, we have $p \nmid L/d$, so $p \nmid L/D_{\rm sym}$, meaning $S_p \ne \{0\}$. Choose a nonzero class $r \bmod p$ such that $br \bmod p \in S_p$ (possible since $b$ is invertible modulo $p$).
  * For each prime $p \mid d$ with $p \mid b$, prescribe $r \equiv 1 \pmod p$.

  By the Chinese remainder theorem, there is an integer $r$ satisfying all congruences modulo $P_d = \prod_{p \mid d} p$ with $|r| \le P_d/2 \le d/2$. Since $r \not\equiv 0 \pmod p$ for every $p \mid d$, we have $r \ne 0$ and $\gcd(r, d) = 1$. Finally, check $h = br$ at every prime $p \le N$: if $p \mid b$ then $h \equiv 0 \in S_p \pmod p$; if $p \nmid b$ then $p \mid d$ and $br \bmod p \in S_p$ by construction. Thus both $1 - |r|/d$ and $1 + |r|/d$ belong to $E_N$. $\square$
