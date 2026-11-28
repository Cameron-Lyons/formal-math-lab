# The reduced numerator and denominator of an improvement

Whenever adding a new denominator $n$ improves the closest approximation to $1$, write the improvement factor in lowest positive terms as
$$
\frac{\delta(n)}{\delta(n-1)} = \frac{a_n}{b_n} \qquad (\gcd(a_n, b_n) = 1,\; 0 < a_n \le b_n).
$$
Suppose Erdős Problem #311 has a positive limiting rate $H_n / n \to c > 0$, where $H_n = -\log \delta(n)$. Then the individual logarithmic jump $g_n = H_n - H_{n-1} = \log(b_n / a_n)$ must satisfy $g_n = o(n)$—meaning $a_n$ and $b_n$ are close to each other on the logarithmic scale. You might wonder whether improvements can happen through modest rational ratios (like $2/3$ or $1000/1001$, or even subexponential integers $a_n, b_n = e^{o(n)}$).

**Surprisingly, the answer is no:** jumps with subexponential reduced numerator and denominator contribute only $o(X)$ to $-\log \delta(X)$ in total—unconditionally! And if $H_n / n \to c > 0$, then **almost all** of the decay of $\delta(n)$ in every dyadic interval must come from jumps where *both* $a_n$ and $b_n$ are exponentially large ($a_n, b_n \ge e^{\kappa n}$), even though their ratio $b_n / a_n = e^{o(n)}$ is tiny by comparison.

---

## Statements of the main results

Let $\delta(n)$ be the least nonzero distance from $1$ to a sum of distinct reciprocals with denominators in $[1, n]$. Write $H_n = -\log \delta(n)$ and $g_n = H_n - H_{n-1} \ge 0$ for $n \ge 2$. For any nonzero rational $a/b$ in lowest terms (with $b > 0$), define its **height** by
$$
\operatorname{ht}(a/b) = \max(|a|, b).
$$

**Theorem 1 (Subexponential jumps are negligible).** For **any** function $h(n) = o(n)$,
$$
\sum_{\substack{2 \le n \le X \\ \log \operatorname{ht}(\delta(n)/\delta(n-1)) \le h(n)}} g_n = o(X).
\tag{1}
$$

**Theorem 2 (Exponentially large reduced terms under a positive rate).** If $H_n / n \to c > 0$, there exists a constant $\kappa = \kappa(c) > 0$ such that, writing $\delta(n)/\delta(n-1) = a_n/b_n$ in lowest positive terms, for every fixed $\lambda > 1$:
$$
\sum_{\substack{X < n \le \lambda X \\ a_n \ge e^{\kappa n},\; b_n \ge e^{\kappa n}}} g_n
= c(\lambda - 1) X + o(X).
\tag{2}
$$
Under the same hypothesis $H_n / n \to c$, the quotient satisfies $\log(b_n/a_n) = g_n = o(n)$, so (2) shows that the two reduced integers $a_n, b_n$ must *both* be exponentially large even while sitting very close together on the logarithmic scale.

---

## A ratio of two signed errors

**The big idea.** Take any two attainable signed errors $u, v$ at cutoff $N$ with $|u| \le e^{-\alpha N}$. Because $|u|$ is exponentially tiny, its reduced denominator $q$ must be at least $e^{\alpha N}$, which forces $q$ to be divisible by a huge product of *large* primes $p > N/(K+1)$. Modulo each such prime $p$, both $Dpu$ and $Dpv$ can only come from the few multiples $p, 2p, \ldots, Kp$, so they land in a *fixed finite set* $A$ of integers (with $Dpu \not\equiv 0 \pmod p$ since $p \mid q$). Writing $u/v = a/b$ in lowest terms gives $p \mid bx - ay$ for some $x \in A \setminus \{0\}$ and $y \in A$. Unless $a/b$ happens to equal one of the finitely many "exceptional ratios" $x/y \in R_K$, the product $\prod |bx - ay|$ over all pairs $(x, y)$ is a **nonzero integer** divisible by every one of those large primes—forcing $\operatorname{ht}(a/b)$ to be exponential in $N$!

Let us formalize this precisely. An **admissible signed error** at $N$ is a nonzero rational of the form $\sum_{i \in I} 1/i - 1$ with $I \subseteq [1, N]$. Fix $\alpha > 0$ and an integer $K \ge 1$ large enough that $1/(K + 1) < \alpha$. Define the fixed finite sets
$$
D = \operatorname{lcm}(1, \ldots, K), \qquad
A = \left\{ D \sum_{i \in I} \frac{1}{i} : I \subseteq [1, K] \right\}, \qquad
R_K = \left\{ \frac{x}{y} : x, y \in A \setminus \{0\} \right\}.
$$
Notice that every element of $A$ is a nonnegative integer (and every element of $R_K$ is strictly positive).

**Lemma (Height dichotomy for ratios of errors).** For any two admissible signed errors $u, v$ at $N$ with $|u| \le e^{-\alpha N}$, either $u/v \in R_K$, or
$$
\log \operatorname{ht}(u/v)
\ \ge\
\frac{\alpha - 1/(K + 1) - o(1)}{(|A| - 1)|A|}\, N.
\tag{3}
$$
Here $K$ is fixed and the $o(1)$ term is uniform over all admissible $u, v$. In particular, if $u$ and $v$ have opposite signs, then $u/v < 0 \notin R_K$, so (3) always holds.

**Proof.**
1. **Extract the large prime divisors of the denominator of $u$.** Let $q$ be the reduced denominator of $u$. Since $u$ is a nonzero rational with denominator dividing $L_N = \operatorname{lcm}(1, \ldots, N)$, its nonzero numerator has magnitude at least $1$, so $1/q \le |u| \le e^{-\alpha N}$, giving $q \ge e^{\alpha N}$.

   How much of $q$ can come from primes $p \le N/(K+1)$ or higher prime powers $p^j$ ($j \ge 2$)? By the prime number theorem and the bound $O(\sqrt{N} \log^2 N)$ for higher prime powers up to $N$,
   $$
   \vartheta\!\left(\frac{N}{K + 1}\right) + \sum_{\substack{p^j \le N \\ j \ge 2}} \log p
   = \frac{N}{K + 1} + o(N).
   $$
   For sufficiently large $N$, every prime $p > N/(K+1)$ divides $L_N$ (and hence $q$) to exponent at most $1$. Dividing out the small-prime and higher-power parts shows that the product $P_u$ of all primes $p > N/(K+1)$ dividing $q$ satisfies
   $$
   \log P_u \ge \left(\alpha - \frac{1}{K + 1} - o(1)\right) N.
   $$
2. **Reduce $Dpu$ and $Dpv$ modulo $p$.** Fix any prime $p \mid P_u$. Since $p > N/(K+1)$ and $N$ is large, $p > K$ (so $p \nmid D$) and $p^2 > N$. Therefore $Dpu$ and $Dpv$ have denominators coprime to $p$ and can be reduced modulo $p$. In $Dpu = Dp(\sum_{i \in I} 1/i - 1)$, the term $-Dp$ and every term with $p \nmid i$ vanish modulo $p$; only multiples $ip$ with $1 \le i \le K$ survive, each contributing $Dp/(ip) = D/i$. Hence
   $$
   Dpu \equiv x \pmod p \qquad \text{and} \qquad Dpv \equiv y \pmod p
   $$
   for some $x, y \in A$. Crucially, $x \ne 0$: because $p \mid q$ (the *reduced* denominator of $u$) and $p \nmid D$, the integer $Dpu \bmod p$ cannot vanish! (For $N$ large enough that $p > \max A$, $x \equiv 0 \pmod p$ is equivalent to $x = 0$.)
3. **Multiply all candidate linear forms.** Write $u/v = a/b$ in lowest terms (with $b > 0$). Clearing denominators in $bu = av$ gives $b(Dpu) = a(Dpv)$, and reducing modulo $p$ yields
   $$
   p \mid bx - ay.
   $$
   (Notice this holds even if $p \mid b$!) Now suppose $a/b \notin R_K$:
   * If $x > 0$ and $y = 0$, then $bx - ay = bx \ne 0$.
   * If $x > 0$ and $y > 0$, then $bx - ay = 0$ would imply $a/b = x/y \in R_K$, impossible.

   Therefore every single factor in the product
   $$
   \Pi := \prod_{x \in A \setminus \{0\}} \ \prod_{y \in A} |bx - ay|
   $$
   is a **positive integer**! There are $(|A| - 1)|A|$ factors, each bounded above by $|b| \max A + |a| \max A \le 2(\max A) \operatorname{ht}(u/v)$. Since every prime $p \mid P_u$ divides at least one factor—hence divides $\Pi$—we have $P_u \mid \Pi$, so $P_u \le \Pi$. Taking logarithms yields
   $$
   \left(\alpha - \frac{1}{K + 1} - o(1)\right) N
   \le \log P_u
   \le \log \Pi
   \le (|A| - 1)|A| \bigl(\log \operatorname{ht}(u/v) + \log(2 \max A)\bigr).
   $$
   Dividing by $(|A| - 1)|A|$ absorbs the constant $\log(2 \max A)$ into $o(1)$ and proves (3). $\square$

---

## Summing the jumps

For each $n \ge 1$, pick an admissible signed error $u_n$ attaining $|u_n| = \delta(n)$. Both $u_n$ and $u_{n-1}$ are admissible at $N = n$, and $\operatorname{ht}(u_n/u_{n-1}) = \operatorname{ht}(\delta(n)/\delta(n-1))$.

### Jumps with ratio in $R_K$ contribute $o(X)$

If $u_n / u_{n-1} \in R_K$, then $|u_{n-1}/u_n| = y/x$ for some $x, y \in A \setminus \{0\}$, so its logarithmic jump is bounded by a constant depending only on $K$:
$$
0 \le g_n = \log \frac{|u_{n-1}|}{|u_n|}
\le \log\!\left(\frac{\max(A \setminus \{0\})}{\min(A \setminus \{0\})}\right)
= \log\!\left(K \sum_{i=1}^K \frac{1}{i}\right).
$$
(Indeed, $\min(A \setminus \{0\}) = D/K$ and $\max(A \setminus \{0\}) = D \sum_{i=1}^K 1/i$.) Meanwhile, for all large $n$, a strict jump ($g_n > 0$) requires a change in $E_n \cap [3/4, 5/4]$, and by the [change-index count](change-indices.md) there are only $O(X \log\log X / \log X) = o(X)$ change indices up to $X$. Multiplying a bounded jump size by $o(X)$ occurrences shows that **all jumps with $u_n/u_{n-1} \in R_K$ contribute $o(X)$ in total up to $X$**.

### Proof of Theorem 1: equation (1)

Fix an arbitrary $\alpha > 0$, and split the indices $2 \le n \le X$ with $\log \operatorname{ht}(\delta(n)/\delta(n-1)) \le h(n)$ into two regimes:
1. **Indices with $H_n < \alpha n$:** Let $n^*$ be the largest index $\le X$ satisfying $H_{n^*} < \alpha n^*$. Since $g_n \ge 0$ and $H_1 = 0$, the sum of *all* $g_n$ over this regime is at most
   $$
   \sum_{n = 2}^{n^*} g_n = H_{n^*} < \alpha n^* \le \alpha X.
   $$
2. **Indices with $H_n \ge \alpha n$ (i.e., $|u_n| \le e^{-\alpha n}$):** Fix $K$ with $1/(K+1) < \alpha$. Since $h(n) = o(n)$ while the right-hand side of (3) grows linearly in $n$, every sufficiently large index in this regime satisfies $\log \operatorname{ht}(u_n/u_{n-1}) \le h(n) < \frac{\alpha - 1/(K+1) - o(1)}{(|A|-1)|A|} n$, so the lemma forces $u_n / u_{n-1} \in R_K$. As just shown, these indices contribute $o(X)$ in total.

Adding the two regimes, dividing by $X$, and letting $X \to \infty$ gives a $\limsup$ of at most $\alpha$. Since $\alpha > 0$ was arbitrary, letting $\alpha \to 0$ proves (1). $\square$

### Proof of Theorem 2: equation (2)

Assume $H_n / n \to c > 0$. Take $\alpha = c/2$ and fix $K$ with $1/(K+1) < \alpha$. Then every sufficiently large $n$ satisfies $|u_n| \le e^{-\alpha n}$. Write $\delta(n)/\delta(n-1) = a_n/b_n$ in lowest positive terms; since $\delta(n) \le \delta(n-1)$, we have $0 < a_n \le b_n$, so $\operatorname{ht}(u_n/u_{n-1}) = b_n$.

* For every sufficiently large $n$ with $u_n / u_{n-1} \notin R_K$, inequality (3) gives $\log b_n \ge 2 \kappa n$ for some constant $\kappa = \kappa(c) > 0$. Moreover, $g_n / n = H_n / n - H_{n-1} / n \to c - c = 0$, so $g_n \le \kappa n$ for all sufficiently large $n$, which immediately gives
  $$
  \log a_n = \log b_n - g_n \ge 2\kappa n - \kappa n = \kappa n.
  $$
  Thus *both* $a_n \ge e^{\kappa n}$ and $b_n \ge e^{\kappa n}$ hold!
* The remaining jumps in $(X, \lambda X]$, which have $u_n / u_{n-1} \in R_K$, contribute $o(X)$ in total.

Since the full sum of $g_n$ over $X < n \le \lambda X$ telescopes to $H_{\lfloor \lambda X \rfloor} - H_{\lfloor X \rfloor} = c(\lambda - 1) X + o(X)$, subtracting the $o(X)$ contribution from $R_K$ proves (2). Whether such exponentially large rational jumps actually occur at the scales required for a positive limiting rate remains unknown. [Erdős Problem 311](https://www.erdosproblems.com/311) $\square$
