# When the attainable sums near 1 change

As you raise the denominator cutoff $n$ one integer at a time, you might expect each new unit fraction $1/n$ to produce fresh sums close to $1$. Surprisingly, almost all integers $n$ add **nothing at all** near $1$!

Let $E_n$ be the set of subset sums of $\{1, 1/2, \ldots, 1/n\}$, and define the local window around $1$ by
$$
J_n = E_n \cap [3/4, 5/4].
$$
An integer $n$ is a **change index** if $J_n \ne J_{n-1}$. Because $1 + 1/(n-1) \in J_{n-1}$ once $n \ge 5$, every strict improvement in the closest gap $\delta(n)$ must occur at a change index (though a change index can also introduce a sum far from the current best approximation).

**Main theorem.** For each fixed $\lambda > 1$, as $X \to \infty$,
$$
\#\{X < n \le \lambda X : J_n \ne J_{n-1}\} \sim (\lambda - 1)\frac{X \log\log X}{\log X}.
$$
Consequently, the total number of change indices up to $X$ is asymptotic to $X \log\log X / \log X$—a zero-density subset of the integers. An exact prime-power characterization of the change indices even pins down the second-order term in this count, and forces any positive exponential decay rate of $\delta(n)$ to be carried by large average jumps of size $\asymp \log X / \log\log X$ at the change indices.

---

## An upper bound on the cofactor

**The big idea.** By the [prime residue criterion](prime-residues.md), passing from $n - 1$ to $n$ can enlarge $J_n$ only if it either introduces a new prime power (enlarging the LCM $L_n = \operatorname{lcm}(1, \ldots, n)$) or enlarges the allowed modulo-$p$ residue set at some prime $p$ whose maximal power $q_p$ divides $n$. Writing $n = j q_p$, adding the $j$th multiple of $q_p$ only matters if the first $j - 1$ multiples did not *already* cover all of $\mathbb{F}_p$. Once $j$ exceeds roughly $\log p \, (\log\log p)^5$, the reciprocals $1, 1/2, \ldots, 1/j$ already cover every residue modulo $p$, so $n$ is guaranteed to leave $J_n$ unchanged!

### The modular covering threshold $B_p(k)$

For a prime $p$ and $0 \le k < p$, let $B_p(k) \subseteq \mathbb{F}_p$ be the set of all subset sums of $1, 1/2, \ldots, 1/k$ in $\mathbb{F}_p$, with $B_p(0) = \{0\}$.

**Lemma (Covering $\mathbb{F}_p$ with small reciprocals).** For all sufficiently large primes $p$,
$$
B_p(K) = \mathbb{F}_p, \qquad \text{where} \qquad K = \left\lceil \log p \, (\log\log p)^5 \right\rceil.
$$

*Proof.* Set $S = cK / ((\log K)^3 (\log\log K)^4)$ with the constant $c$ from Liu and Sawhney's Lemma 4.1, and put $Q = \operatorname{lcm}(1, \ldots, \lfloor S \rfloor)$. Because $(\log\log p)^5$ beats $(\log K)^3 (\log\log K)^4 \asymp (\log\log p)^3 (\log\log\log p)^4$, we have $S/\log p \to \infty$ while $S < K < p$. By the prime number theorem, $\log Q \sim S$, so $Q > p^2$ and $p \nmid Q$ (every prime dividing $Q$ is at most $S < p$).

For every integer $s \in [Q/3, Q]$, Liu and Sawhney's Lemma 4.1 represents $s/Q$ using distinct unit fractions with denominators at most $K$ (since every prime power dividing $Q$ is at most $S$). Because $Q > p^2$, the interval $[Q/3, Q]$ contains at least $p$ consecutive integers $s$. Reducing $s/Q$ modulo $p$ (where $Q$ is invertible) hits every residue class in $\mathbb{F}_p$, proving $B_p(K) = \mathbb{F}_p$. [Liu and Sawhney, Lemma 4.1](https://arxiv.org/html/2404.07113v1#S4) $\square$

### Exact characterization of change indices

Write $L_n = \operatorname{lcm}(1, \ldots, n)$, and for each prime $p \le n$ let $q_p$ be the largest power of $p$ at most $n$. By the [prime residue criterion](prime-residues.md), for all sufficiently large $n$, a point $1 + h/L_n$ with $|h| \le L_n/4$ belongs to $J_n$ if and only if for every prime $p \le n$,
$$
h \bmod p \in \frac{L_n}{q_p}\, B_p\bigl(\lfloor n / q_p \rfloor\bigr).
$$
Note that $\lfloor n/q_p \rfloor < p$ by maximality of $q_p$, and $L_n/q_p$ is invertible modulo $p$.

Now define the **modular covering threshold** for each prime $p$:
$$
f(p) = \min\bigl\{k \ge 1 : B_p(k) = \mathbb{F}_p\bigr\}.
$$
This minimum always exists (and satisfies $f(p) \le p - 1$) because the single reciprocals $1/1, 1/2, \ldots, 1/(p-1)$ already supply every nonzero residue in $\mathbb{F}_p$.

**Theorem (Exact change-index criterion).** For all sufficiently large $n$,
$$
J_n \ne J_{n-1}
\quad \Longleftrightarrow \quad
n = j p^a \quad \text{for a prime } p,\; a \ge 1,\; 1 \le j \le f(p).
$$
Furthermore, because $j \le f(p) < p \le p^a$, the prime power $q = p^a$ in such a factorization automatically satisfies $q > \sqrt{n}$ and is the unique largest power of $p$ at most $n$, making the factorization $(j, p, a)$ **unique**.

*Proof.*
* **Sufficiency ($\Leftarrow$).** Suppose $n = j q$ with $q = p^a > \sqrt{n}$ and $1 \le j \le f(p)$. By definition of $f(p)$, $B_p(j-1)$ is a proper subset of $\mathbb{F}_p$. Since $1/j \not\equiv 0 \pmod p$, translating $B_p(j-1)$ by $1/j$ cannot keep it fixed (otherwise $B_p(j-1)$ would be closed under addition by $1/j$, hence all of $\mathbb{F}_p$). Therefore $B_p(j)$ contains a new residue $r \notin B_p(j-1)$, attained by some subset $I \subseteq \{1, \ldots, j\}$.

  Form the sum
  $$
  t = 1 + \sum_{i \in I} \frac{1}{iq} \in E_n.
  $$
  Since $q > \sqrt{n}$, we have $0 \le t - 1 \le (1 + \log n)/\sqrt{n} \le 1/4$ for large $n$, so $t \in J_n$. Modulo $p$, $q t \equiv r \pmod p$. Could $t$ already lie in $J_{n-1}$? In any representation of $t$ using denominators at most $n - 1$, every denominator with $p$-adic valuation strictly less than $a$ contributes $0$ to $qt \bmod p$, while the only denominators up to $n - 1$ divisible by $q = p^a$ are $iq$ with $1 \le i \le j - 1$, whose sums only produce residues in $B_p(j - 1)$. Since $r \notin B_p(j - 1)$, we have $t \notin J_{n-1}$, so $J_n \ne J_{n-1}$.
* **Necessity ($\Rightarrow$).** If $n = p^a$ is itself a prime power, take $j = 1 \le f(p)$. Otherwise, $n$ is not a prime power, so moving from $n - 1$ to $n$ leaves both $L_n$ and every maximal prime power $q_p$ completely unchanged. In the prime residue criterion, the condition at a prime $p$ can only relax if $\lfloor n / q_p \rfloor > \lfloor (n - 1)/q_p \rfloor$—that is, if $q_p \mid n$—and if $B_p(\lfloor n/q_p \rfloor - 1)$ was still a proper subset of $\mathbb{F}_p$. Writing $n = j q_p$, this says precisely $1 \le j \le f(p)$. $\square$

### Necessary cofactor bound on $(X, \lambda X]$

Combining necessity with the lemma $f(p) \le \lceil \log p \, (\log\log p)^5 \rceil$ (and enlarging the constant $C$ to absorb the finitely many small primes, where $j < p$, as well as the fixed factor $\lambda$ in $n \le \lambda X$) yields a clean necessary condition: for all sufficiently large $X$, any change index $n \in (X, \lambda X]$ must satisfy
$$
n = j p^a, \qquad a \ge 1, \qquad j \le T_X := C \log X \, (\log\log X)^5.
$$
(Prime powers themselves satisfy this with $j = 1$.)

---

## A range in which every index changes the set

For a matching lower bound, consider all integers $n = jp \in (X, \lambda X]$ where $p$ is prime and
$$
1 \le j \le \frac{1}{2} \log X.
$$
For large $X$, $p = n/j > X / (\frac{1}{2}\log X) > \sqrt{\lambda X}$, and a trivial subset count bounds $B_p(j - 1)$ by
$$
|B_p(j - 1)| \le 2^{j - 1} \le 2^{\frac{1}{2}\log X} = X^{\frac{\log 2}{2}} < p
$$
(since $\frac{\log 2}{2} < 1/2$). Hence $B_p(j - 1) \ne \mathbb{F}_p$, which means $j \le f(p)$. By the exact characterization, **every** such integer $n = jp$ changes $J_n$.

---

## Counting the indices

We now sandwich the number of change indices in $(X, \lambda X]$ between our lower range ($j \le \frac{1}{2}\log X$) and our upper range ($j \le T_X$).

1. **Higher prime powers ($a \ge 2$) are negligible.** In the upper bound, how many integers $n = j p^a \le \lambda X$ have $a \ge 2$ and $j \le T_X$? There are $O_\lambda(\log X)$ possible exponents $a \ge 2$, at most $O_\lambda(\sqrt{X})$ primes $p$ for each, and at most $T_X$ choices for $j$, giving at most $O_\lambda(T_X \sqrt{X} \log X)$ indices in total—far smaller than $X \log\log X / \log X$.
2. **Simple multiples ($a = 1$) have unique $(j, p)$.** For $n = jp \in (X, \lambda X]$ with $j \le T_X$, we have $p > X/T_X > \sqrt{\lambda X}$ for large $X$, so no integer can be written as $jp$ in two different ways.
3. **Evaluate the prime count.** For either cutoff $U = \frac{1}{2}\log X$ or $U = T_X = C \log X \, (\log\log X)^5$, the prime number theorem gives
   $$
   \begin{aligned}
   \sum_{j \le U} \bigl(\pi(\lambda X / j) - \pi(X / j)\bigr)
     &= (1 + o(1)) \frac{(\lambda - 1) X}{\log X} \sum_{j \le U} \frac{1}{j} \\
     &\sim \frac{(\lambda - 1) X \log\log X}{\log X}.
   \end{aligned}
   $$
   The relative error is uniform over $1 \le j \le U$ because $X/j \ge X/T_X \to \infty$, $\lambda > 1$ is fixed, and $\log(X/j) \sim \log X$ uniformly. Crucially, *both* cutoffs have the exact same leading logarithm:
   $$
   \log\!\left(\frac{1}{2}\log X\right) \sim \log\log X \qquad \text{and} \qquad \log T_X \sim \log\log X.
   $$
   Thus the lower and upper bounds agree asymptotically, proving the main theorem on $(X, \lambda X]$.

4. **Count up to $X$.** Sum the dyadic estimate ($\lambda = 2$) over intervals $(X/2^{k+1}, X/2^k]$ down to $X / (\log X)^2$. All integers below $X / (\log X)^2$ contribute at most $X / (\log X)^2 = o(X \log\log X / \log X)$, and $\log\log y / \log y \sim \log\log X / \log X$ uniformly on the retained range, yielding $\#\{n \le X : J_n \ne J_{n-1}\} \sim X \log\log X / \log X$.

*Distribution of cofactor sizes.* For any fixed $0 < \theta < 1$, all integers $n = jp \in (X, \lambda X]$ with $j \le (\log X)^\theta$ fall inside the lower-bound range for large $X$. The same prime sum yields $(\theta + o(1))(\lambda - 1) X \log\log X / \log X$ such change indices, so the fraction of change indices with cofactor $j \le (\log X)^\theta$ converges to $\theta$.

---

## The second term in the count

Because the exact change-index criterion depends on $f(p)$, pinning down $f(p)$ more tightly immediately yields a **second-order asymptotic term** for the number of change indices.

Write $L_1(x) = \log x$ and $L_{i+1}(x) = \log L_i(x)$.

**Proposition (Bounds on $f(p)$).** For all sufficiently large primes $p$,
$$
\frac{L_1(p) L_2(p)}{L_3(p)} \ll f(p) \ll L_1(p) L_2(p) L_3(p)^2.
$$

*Proof.*
* **Lower bound:** Reducing rational reciprocal sums modulo $p$ maps $E_{f(p)}$ onto $B_p(f(p)) = \mathbb{F}_p$, so $p \le |E_{f(p)}|$. By the elementary [distinct-sum count](largest-grid.md#size-of-the-largest-grid), $\log |E_k| \ll k \log\log k / \log k$. At $k = \lfloor c L_1(p) L_2(p) / L_3(p) \rfloor$ for a sufficiently small constant $c > 0$, we have $\log k \sim L_2(p)$ and $\log\log k \sim L_3(p)$, so $\log |E_k| < \log p$, giving $|E_k| < p$ and forcing $f(p) > k$.
* **Upper bound:** Apply the [three-stage grid construction](README.md#four-applications) at scale $x = 6 \log p$. It produces a denominator $D \ge e^{x/3} = p^2$ with all prime factors at most $x < p$ (so $p \nmid D$), realizing every $s/D \in [3/8, 1]$ using distinct denominators at most $O(x \log x (\log\log x)^2) = O(L_1(p) L_2(p) L_3(p)^2)$. Since $[3D/8, D]$ contains more than $p$ consecutive integers, reducing $s/D$ modulo $p$ covers all of $\mathbb{F}_p$. $\square$

### Sharpening the change count

For $n = jp \in (X, \lambda X]$ in our counting ranges, $\log p \sim \log X$ uniformly. The exact criterion therefore sandwiches the prime count (up to the same negligible higher-power term) between the two polylogarithmic cutoffs
$$
U_- = \frac{c L_1(X) L_2(X)}{L_3(X)} \qquad \text{and} \qquad U_+ = C L_1(X) L_2(X) L_3(X)^2.
$$
Using the sharper prime number theorem $\pi(y) = y/\log y + O(y/(\log y)^2)$ together with $\sum_{j \le U} 1/j = \log U + O(1)$, we have uniformly for any polylogarithmic cutoff $U$:
$$
\sum_{j \le U} \bigl(\pi(\lambda X / j) - \pi(X / j)\bigr)
= \frac{(\lambda - 1) X}{\log X}\bigl(\log U + O_\lambda(1)\bigr).
$$
(Replacing $1/\log(X/j)$ by $1/\log X$ introduces a relative error of $O(\log j / \log X)$, which adds $O_\lambda((\log U)^2 / \log X) = o(1)$ inside the parentheses.) Taking logarithms of $U_-$ and $U_+$ gives $\log U_\pm = L_2(X) + L_3(X) + O(L_4(X))$, and therefore
$$
\#\{X < n \le \lambda X : J_n \ne J_{n-1}\}
= \frac{(\lambda - 1) X}{\log X}\bigl(L_2(X) + L_3(X) + O_\lambda(L_4(X))\bigr).
$$
Dyadic summation down to $y = X / (\log X)^2$ transfers the same expansion (with prefactor $X/\log X$) to the cumulative count through $X$: on $[X/(\log X)^2, X]$, $1/\log y$ differs from $1/\log X$ by a relative $O(L_2(X)/\log X)$ and $L_i(y) = L_i(X) + o(1)$ uniformly for $2 \le i \le 4$, while the discarded tail below $X/(\log X)^2$ is $o(X/\log X)$.

---

## Consequence for an exponential rate

Define the single-step logarithmic improvement
$$
g_n = \log \frac{\delta(n-1)}{\delta(n)} \ge 0.
$$
* **Under a limiting rate:** Suppose $-\log \delta(n)/n \to c > 0$. Telescoping gives
  $$
  \sum_{X < n \le \lambda X} g_n = c(\lambda - 1) X + o(X).
  $$
  For large $X$, $g_n = 0$ at every non-change index ($J_n = J_{n-1}$). Dividing the total gain by the number of change indices shows that the **mean** of $g_n$ over change indices in $(X, \lambda X]$ must be
  $$
  (c + o(1))\frac{\log X}{\log\log X}.
  $$
  In particular, every sufficiently large dyadic interval must contain a single-step drop in $\log \delta$ of at least this order. Knowing *where* changes happen leaves open *how large* the actual improvements $g_n$ are, which is what would decide the existence of a positive limiting rate. [Erdős Problem #311](https://www.erdosproblems.com/311)

* **Without assuming convergence:** Even without any limit assumption,
  $$
  \limsup_{X \to \infty} \frac{-\log \delta(X)}{X}
  \le \limsup_{n \to \infty} \frac{\log\log n}{\log n}\, g_n.
  $$
  *Proof.* The sum of $\log n / \log\log n$ over all change indices $3 \le n \le X$ is asymptotic to $X$: on $[X/(\log X)^2, X]$ each summand is uniformly asymptotic to $\log X / \log\log X$ and there are $(1 + o(1)) X \log\log X / \log X$ change indices, while summing even over *every* integer below $X/(\log X)^2$ contributes $o(X)$. If the right-hand $\limsup$ is finite—call it $M$—then for any $\varepsilon > 0$ we eventually have $g_n \le (M + \varepsilon) \log n / \log\log n$ at every change index (and $g_n = 0$ elsewhere). Summing up to $X$, telescoping $-\log \delta(X) = \sum_{n=2}^X g_n$, dividing by $X$, and letting $\varepsilon \to 0$ proves the inequality.

  In particular, a uniform bound $g_n = o(\log n / \log\log n)$ would immediately force $-\log \delta(X)/X \to 0$.
