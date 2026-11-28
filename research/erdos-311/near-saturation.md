# When an individual reciprocal sum approaches the LCM bound

Every sum of distinct unit fractions with denominators up to $n$ is an integer multiple of $1/L_n$, where $L_n = \operatorname{lcm}(1, \ldots, n)$. Thus $1/L_n$ is the absolute theoretical floor on the closest nonzero miss $\delta(n)$. Write
$$
h_n = L_n \delta(n) \in \mathbb{Z}_{\ge 1}
$$
for the integer numerator of the gap over $L_n$.

How often can an approximation nearly **saturate** the LCM bound—meaning $h_n = 1$, or $h_n \le n^K$, or more generally $h_n \le e^{o(n)}$? We prove that near-saturation is extremely rare (natural density $0$, and at most $O_K(X^{0.525})$ up to $X$ in the polynomial regime), show that any near-saturated approximation forces $\delta$ to remain flat for at least a $20\%$ stretch, and certify $h_n > n^5$ for every $1{,}000 \le n \le 1{,}000{,}000$.

## Summary of results

* **Density zero for subexponential $h_n$:** For any function $g(n) = o(n)$,
  $$
  \#\{n \le X : h_n \le \exp(g(n))\} = o(X).
  $$
  In particular, the exact LCM floor $\delta(n) = 1/L_n$ can occur only on a set of natural density zero.
* **Sharper count for polynomial $h_n$:** For every fixed $K \ge 0$, combining the same divisibility obstruction with Baker, Harman, and Pintz's prime-gap theorem yields
  $$
  \#\{n \le X : h_n \le n^K\} = O_K(X^{0.525}).
  $$
* **Forced plateau:** Along any sequence where $h_n = \exp(o(n))$, for any fixed $0 < \eta < 1/5$ and sufficiently large $n$ in the sequence, $\delta(m) = \delta(n)$ throughout $n \le m \le (6/5 - \eta)n$.
* **Finite certificate:** An exact residue sieve proves $h_n > n^5$ for **every** integer $1{,}000 \le n \le 1{,}000{,}000$ inclusive.

*(Note: neither the density-zero theorem nor the finite sieve rules out infinitely many exceptions.)*

---

## A divisibility condition at two indices

**The big idea.** Suppose two cutoffs $n \le m < 2n$ both achieve very tight approximations to $1$. Any prime $p$ in the overlap window $(m/2, n]$ has only *one* multiple up to $m$—namely $p$ itself! So modulo $p$, the scaled error at $n$ is either $0$ or $L_n/p$, and the scaled error at $m$ is either $0$ or $L_m/p$. Comparing them after rescaling by $R = L_m/L_n$ shows that every prime in $(m/2, n]$ must divide the product $ab(Ra - b)$. If $Ra \ne b$, this forces $m/n$ to jump well away from $1$; if $Ra = b$, the two approximations are *identical*, which forces $m$ and $n$ to be very close together!

Let us make this exact. For each $n$, fix a subset $A_n \subseteq \{1, \ldots, n\}$ attaining $\delta(n)$, and let
$$
a_n = L_n \left(\sum_{j \in A_n} \frac{1}{j} - 1\right) \in \mathbb{Z} \setminus \{0\}, \qquad |a_n| = h_n.
$$
Take any pair of indices $n \le m < 2n$, and write $R = L_m/L_n$, $a = a_n$, and $b = a_m$.

**Lemma.** Over primes $p$,
$$
\prod_{m/2 < p \le n} p \ \bigm|\ a b (R a - b).
$$

*Proof.* Fix any prime $p \in (m/2, n]$. Because $2p > m$, the only positive multiple of $p$ up to $m$ (and hence also up to $n$) is $p$ itself. Reducing modulo $p$, every denominator other than $p$ vanishes, so:
* $a \equiv 0 \text{ or } L_n/p \pmod p$, depending on whether $p \notin A_n$ or $p \in A_n$;
* $b \equiv 0 \text{ or } L_m/p \pmod p$, depending on whether $p \notin A_m$ or $p \in A_m$.

If $p$ divides neither $a$ nor $b$, then $a \equiv L_n/p$ and $b \equiv L_m/p = R(L_n/p) \pmod p$, which gives $Ra - b \equiv 0 \pmod p$. Hence $p \mid ab(Ra - b)$ in every case. $\square$

(Will Sawin used the same top-interval prime observation to study adjacent changes of the minimum in the #311 discussion. [Sawin's comments, July 2026](https://www.erdosproblems.com/forum/thread/311))

### Logarithmic consequences

Write $\theta(t) = \sum_{p \le t} \log p$ and $\psi(t) = \log L_{\lfloor t \rfloor}$. By the prime number theorem, $\theta(t) = t + o(t)$ and $\psi(t) = t + o(t)$, so $\log R = \psi(m) - \psi(n) = m - n + o(n)$.

* **Case 1: Distinct signed errors ($Ra \ne b$).** Because $ab(Ra - b) \ne 0$, taking logarithms of the divisibility lemma gives
  $$
  \theta(n) - \theta(m/2) \le \log |ab| + \log(R|a| + |b|).
  $$
  If both indices satisfy $\log |a| = o(n)$ and $\log |b| = o(m)$, the left-hand side is $n - m/2 + o(n)$ while the right-hand side is at most $\log R + o(n) = m - n + o(n)$. Rearranging $n - m/2 \le m - n + o(n)$ forces
  $$
  m \ge \left(\frac{4}{3} - o(1)\right) n.
  $$
* **Case 2: Identical signed errors ($Ra = b$).** Then $R = |b|/|a| \le |b|$, so $\log R \le \log |b|$. If $\log |b| = o(n)$, then $m - n + o(n) = \log R = o(n)$, which forces $m = n + o(n)$.

---

## Counting the exceptional indices

### Proof of the density-zero theorem

Fix $g(n) = o(n)$ and call an index $n$ **exceptional** if $\log h_n \le g(n)$.

Consider any sufficiently large block $[Y, 5Y/4]$. Every exceptional index inside $[Y, 5Y/4]$ must have the **exact same** signed minimizing error! Why? Because distinct errors require a ratio $m/n \ge 4/3 - o(1)$, which strictly exceeds the block ratio $5/4$ (and the $o(1)$ errors from the prime number theorem and $g(t) = o(t)$ are uniform across the entire tail).

Now if $[Y, 5Y/4]$ contains at least two exceptional indices, let $n$ and $m$ be the smallest and largest among them. Since their signed errors coincide ($Ra = b$), Case 2 gives $m - n = o(Y)$, so there are at most $m - n + 1 = o(Y)$ exceptional indices in the whole block $[Y, 5Y/4]$.

Finally, partition $[1, X]$ into geometrically shrinking blocks with endpoints $X(4/5)^j$. Since the block lengths sum geometrically to $O(X)$, summing the $o(\text{length})$ counts gives $o(X)$ exceptional indices up to $X$. $\square$

### Proof of the $O_K(X^{0.525})$ bound for $h_n \le n^K$

When $h_n \le n^K$ and $h_m \le m^K$ inside $[Y, 5Y/4]$, equality of signed errors ($Ra = b$) gives
$$
R = \frac{L_m}{L_n} = \frac{|b|}{|a|} \le m^K.
$$
Every prime $p \in (n, m]$ divides $R$ (and exceeds $n$), so if there are $r$ primes in $(n, m]$, then $n^r < R \le m^K$, which means $r < K \log m / \log n = O_K(1)$—only *boundedly many* primes can lie between $n$ and $m$!

By Baker, Harman, and Pintz's prime-gap theorem, every interval $[t - t^{0.525}, t]$ contains a prime for all sufficiently large $t$. Thus any prime-free gap inside $[Y, 5Y/4]$ has length $O(Y^{0.525})$, and having only $O_K(1)$ primes in $(n, m]$ forces $m - n = O_K(Y^{0.525})$. Summing over the geometric partition $X(4/5)^j$ yields $O_K(X^{0.525})$ indices up to $X$. [Baker, Harman and Pintz, Theorem 1](https://doi.org/10.1112/plms/83.3.532) $\square$

---

## How long the minimum must stay constant

What happens immediately *after* a very sharp approximation at $n$? Suppose $n < m < 2n$ and $\delta(m) < \delta(n)$. Then $Ra \ne b$, and monotonicity $\delta(m) < \delta(n)$ means $|b|/L_m < |a|/L_n$, i.e., $|b| < R|a|$. Plugging $|b| \le R|a|$ into the divisibility lemma $\prod_{m/2 < p \le n} p \mid ab(Ra - b)$ gives $|ab(Ra - b)| \le 2 R^2 |a|^3$, so
$$
\theta(n) - \theta(m/2) \le \log 2 + 2 \log R + 3 \log |a|.
$$
Write $u_n = -\log \delta(n)$, so $\log |a| = \psi(n) - u_n$. Substituting $\theta(t) = t + o(t)$, $\psi(t) = t + o(t)$, and $\log R = m - n + o(n)$ yields
$$
n - \frac{m}{2} \le 2(m - n) + 3(n - u_n) + o(n)
\quad \Longrightarrow \quad
\frac{5}{2} m \ge 3 u_n - o(n)
\quad \Longrightarrow \quad
m \ge \frac{6}{5} u_n - o(n).
$$
In particular, along any sequence of indices with $h_n = \exp(o(n))$ (so $u_n = n - o(n)$), for every fixed $0 < \eta < 1/5$ and all sufficiently large $n$ in the sequence, no improvement can happen before $(6/5 - \eta)n$:
$$
\delta(m) = \delta(n) \qquad \text{for every integer } n \le m \le \left(\frac{6}{5} - \eta\right) n.
$$

Note that all of these conclusions govern approximations near the extremal LCM scale $\exp(-(1 + o(1))n)$. A limiting exponential rate $\delta(n) = \exp(-(c + o(1))n)$ with $0 < c < 1$ would instead have $\log h_n = (1 - c + o(1))n$, so the density-zero theorem leaves Erdős Problem #311 open.

---

## Finite certificate by residues

To complement the asymptotic theorems, a fast exact modular sieve certifies
$$
L_n \delta(n) > n^5 \qquad \text{for every integer } 1{,}000 \le n \le 1{,}000{,}000.
$$

**How the sieve works.** Starting at $u = 1{,}000$, partition $[1{,}000, 1{,}000{,}000]$ into consecutive blocks $[u, v]$ with $v = \min(\lfloor 3u/2 \rfloor, 1{,}000{,}000)$. Let $T$ be the set of the **seven greatest primes at most $u$**, and let $P = \prod_{p \in T} p$. The verifier checks explicitly that every prime in $T$ exceeds $v/2$.

Consequently, for *every* $n \in [u, v]$ and every $p \in T$, the only multiple of $p$ up to $n$ is $p$ itself. Therefore, for any subset $A \subseteq [1, n]$, $P$ divides $L_n / j$ unless $j \in T$, so the signed error numerator obeys
$$
L_n \left(\sum_{j \in A} \frac{1}{j} - 1\right)
\equiv \frac{L_n}{P} \sum_{p \in A \cap T} \frac{P}{p} \pmod P.
$$
There are only $2^7 = 128$ choices for $A \cap T$, covering *all* possible residues modulo $P$ of any attainable error numerator at $n$:
* **Empty choice ($A \cap T = \emptyset$):** The error numerator is congruent to $0 \pmod P$, so any *nonzero* numerator has magnitude at least $P$. The verifier checks $P > w^5$, where $w$ is the last index of the current constant-$L_n$ segment.
* **Each of the $127$ nonempty choices:** Compute its canonical residue $0 \le r < P$ and check $\min(r, P - r) > w^5$. Passing this check rules out every nonzero numerator of magnitude at most $n^5$ throughout the entire constant-$L_n$ segment.

**Implementation and audit details.** The verifier generates all prime powers in order: at each prime power $p^a$, $L_n$ acquires a single factor of $p$, updating $(L_n / P) \bmod P$ in $O(1)$ modular arithmetic. At the initial index $n = 1{,}000$, it cross-checks $(L_{1000} / P) \bmod P$ against the direct exact integer LCM. In total, the run certifies all $999{,}001$ indices across $18$ blocks and $78{,}555$ constant-LCM segments (including splits at block boundaries). [Verifier](saturation_sieve.py)

~~~sh
python3 research/erdos-311/saturation_sieve.py
~~~
