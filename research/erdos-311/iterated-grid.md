# A reciprocal-sum grid built with a variable number of prime intervals

In the [four-stage construction](README.md#four-applications), iterating the prime-extension lemma four times produced a complete grid near $1$ with denominator $\log D \gg N / (L_1(N) L_2(N) L_3(N)^2)$. Why stop at four stages? If we let the number of stages grow with $N$—climbing all the way up the tower of iterated logarithms from a fixed constant scale $T$ to the target scale $x$—we remove the squared factor $L_3(N)^2$ and cover the entire symmetric interval $[1/2, 3/2]$ at once.

## Notation and main theorem

Let $E_N$ be the set of sums of distinct reciprocals with positive denominators at most $N$, and let $\delta(N)$ be the least nonzero distance from $1$ to $E_N$. Define the iterated natural logarithms by $L_0(t) = t$ and $L_{j+1}(t) = \log L_j(t)$. Let $B(t)$ be the product of all iterated logarithms $L_1(t), L_2(t), \ldots$ that are at least $2$ (with the empty product equal to $1$):
$$
B(t) = \prod_{\substack{j \ge 1 \\ L_j(t) \ge 2}} L_j(t).
$$
Notice that $B(N) = L_1(N) L_2(N) L_3(N) \cdots$ grows slower than $L_1(N) L_2(N) L_3(N)^2$—in fact, $B(L_3(N)) \le L_4(N)^2$, so $B(N)$ beats the four-stage denominator factor by at least a constant times $L_3(N)/L_4(N)^2 \to \infty$.

**Theorem.** There exists an absolute constant $c > 0$ such that for every sufficiently large $N$, there is an integer $D$ satisfying
$$
\log D \ge c \frac{N}{B(N)}, \qquad \frac{s}{D} \in E_N \quad \text{for every integer } D/2 \le s \le 3D/2.
$$

Taking $s = D - 1$ and $s = D + 1$ realizes **both** $1 - 1/D$ and $1 + 1/D$ simultaneously, giving $\delta(N) \le \exp(-cN/B(N))$ (and the same upper bound for the [symmetric gap](symmetric-gaps.md)). Whether $-\log \delta(N)/N$ tends to a positive constant remains open. [Erdős problem #311](https://www.erdosproblems.com/311)

---

## Adding a prime interval

First, we extend the [prime extension lemma](README.md#how-to-add-primes-to-a-common-denominator) so that the grid covers $[a, 3/2]$ rather than just $[a, 1]$, allowing approximations from *above* $1$ as well as below.

**Lemma.** Let $0 \le a < 1$. Suppose every grid point $m/D \in [a, 3/2]$ can be represented using distinct divisors of $D$ at most $H$ as denominators. Let $\mathcal{P}$ be a finite set of primes coprime to $D$, with product $P$ and largest prime $z$. If the integer interval $[aD, D]$ contains at least $z$ integers, then we obtain a new grid covering $[a', 3/2]$ using divisors of $D'$ at most $H'$, where
$$
D' = DP, \qquad a' = a + \sum_{p \mid P} \frac{1}{p}, \qquad H' = zH.
$$

**Proof.** Given any target $s/(DP) \in [a', 3/2]$, for each prime $p \mid P$ choose an integer $m_p \in [aD, D] \cap \mathbb{Z}$ solving
$$
m_p (P/p) \equiv s \pmod p.
$$
This exists because $P/p$ is invertible modulo $p$ and $[aD, D]$ has at least $z \ge p$ consecutive integers. Subtract $\sum_{p \mid P} m_p / (pD)$ from $s/(DP)$:
* The remaining numerator $s - \sum_{p \mid P} m_p(P/p)$ over $DP$ is divisible by every $p \mid P$, hence by $P$, leaving a grid point $m/D$.
* Because $0 \le m_p / (pD) \le 1/p$ for each $p \mid P$, the total subtracted amount lies in $[0, \sum_{p \mid P} 1/p]$, so $m/D \in [a, 3/2]$.

Now represent $m/D$ and each $m_p/D$ on the old grid (using divisors of $D$ at most $H$), and multiply the denominators of the $m_p/D$ representation by $p$. Each $p$-group contains $p$ and no other prime dividing $P$, while the $m/D$ group contains none of those primes. Hence all groups are disjoint, every denominator divides $DP$, and the largest denominator used is at most $zH$. $\square$

---

## Choosing and adding the primes

**The big idea.** In the four-stage construction, each stage added all primes in $(u/2, u]$, reserving a constant budget of $1/8$ per stage for the upward shift of the lower endpoint $a$. That budget runs out when the number of stages grows to infinity. Instead, at scale $u$ (with previous scale $y = \log u$), we take the prime interval $I(u) = (u/y^2, u(1 + 1/y)]$. Even though $I(u)$ spans $O(\log y)$ dyadic blocks, every prime in it has logarithm $\asymp y$, so each dyadic block contributes only $O(1/y)$ to $\sum 1/p$—making the total reciprocal sum at scale $u$ at most $1/\sqrt{y}$. Across an exponential tower of scales $u$, the values $y = \log u$ grow by at least a factor of $4$ at each step, so $\sum 1/\sqrt{y}$ converges to less than $1/4$ no matter how many stages we run.

### The prime interval $I(u)$

For a large scale $u$, write $y = \log u$ and take all primes in
$$
I(u) = \left(\frac{u}{y^2}, \; u\left(1 + \frac{1}{y}\right)\right].
$$
Let us check its three key properties for all sufficiently large $u$:
1. **Large prime product:** By the prime number theorem with error term $\vartheta(t) = \sum_{p \le t} \log p = t + O(t / \log^2 t)$,
   $$
   \sum_{p \in I(u)} \log p = u + \frac{u}{y} + O\!\left(\frac{u}{y^2}\right) \ge u + 3.
   $$
   [Prime number estimates](https://arxiv.org/abs/2002.11068)
2. **Tiny reciprocal sum:** Cover $I(u)$ by $O(\log y)$ dyadic intervals. On each dyadic interval $(w, 2w]$, $\pi(2w) \ll w/\log w$ and $\log w \asymp y$, so each interval contributes $O(1/y)$ to $\sum 1/p$. Thus the total reciprocal sum over $I(u)$ is $O((\log y)/y) \le 1/\sqrt{y}$.
3. **Clean prime size bounds:** Every prime $p \in I(u)$ satisfies
   $$
   2y < p \le u\left(1 + \frac{1}{y}\right) \le u \exp\!\left(\frac{1}{\sqrt{y}}\right) \qquad \text{and} \qquad p \le 2u.
   $$

### Climbing the logarithmic tower

Fix an absolute constant $T$ large enough that all estimates above hold for every $u \ge T$, and that $2/\sqrt{T} < 1/4$ and $e^t \ge 4t$ for all $t \ge T$.

Start at a large target scale $x$, and take repeated natural logarithms $x, L_1(x), L_2(x), \ldots$ until landing on the last scale $u_0 \in [T, e^T)$. Now build the grid **bottom-up** (in reverse order of the tower):

1. **Base step (scale $u_0 \in [T, e^T)$).** Take a fixed power of two $D_b \ge \exp(e^T + 3)$. Ordinary binary expansion represents every grid point $m/D_b \in [0, 3/2]$ using distinct denominators from $\{1, 2, 4, \ldots, D_b\}$ (since $1 + 1/2 + 1/4 + \cdots + 1/D_b = 2 - 1/D_b > 3/2$). Notice that $D_b \ge \exp(u_0 + 3)$ and its only prime factor is $2 \le 2 u_0$.
2. **Inductive step (passing from scale $y = \log u$ to scale $u$).** At each subsequent scale $u$ along the tower up to $x$, apply the prime-interval lemma using the primes in $I(u)$.
   * **Coprimality:** By induction, all prime factors of the current denominator $D'$ are at most $2y$, whereas every prime in $I(u)$ exceeds $2y$, so all new primes are fresh.
   * **Lower endpoint control:** Along the tower, successive values of $\log u$ increase by at least a factor of $4$ (since $e^t \ge 4t$ for $t \ge T$). Therefore the *total* increase in the lower endpoint $a$ over all stages combined is bounded by a geometric series:
     $$
     \sum_{u} \frac{1}{\sqrt{\log u}} \le \frac{1}{\sqrt{T}} \sum_{k=0}^\infty 2^{-k} = \frac{2}{\sqrt{T}} < \frac{1}{4}.
     $$
     In particular, the lower endpoint stays strictly below $1/4$ throughout, so the old grid always covers $[1/2, 1]$.
   * **Enough consecutive integers:** By the base choice or the prime-product bound at scale $y = \log u$, the current denominator satisfies $D' \ge \exp(y + 3) = e^3 u$. Hence $[D'/2, D']$ contains at least $\frac{1}{2} e^3 u > 2u$ integers—more than enough for every prime in $I(u)$, all of which are $\le 2u$.
   * **New invariants:** After adding $I(u)$, the new denominator $D' P$ has logarithm at least $u + 3$, all its prime factors are at most $2u$, and it still covers $[1/2, 3/2]$.

### Bounding the largest denominator and choosing $x$

When the tower finishes at scale $x$, we have a denominator $D$ (divisible by $4$ from the base $D_b$) with $\log D \ge x + 3$, all prime factors at most $2x$, and a complete grid covering $[1/2, 3/2]$ using divisors of $D$.

What is the largest unit-fraction denominator used? At each extension scale $u$, the maximum denominator multiplies by $\max I(u) \le u \exp(1/\sqrt{\log u})$. The product of the scales $u$ where primes were added is at most $x B(x)$ (since $x$ is the top scale and every smaller scale is an iterated logarithm $L_j(x) \ge T \ge 2$), and $\sum_u 1/\sqrt{\log u} < 1/4$. Therefore the largest denominator used is at most
$$
D_b \prod_u \left(u \exp\!\left(\frac{1}{\sqrt{\log u}}\right)\right) \le C x B(x), \qquad C = e^{1/4} D_b.
$$

Finally, set
$$
x = \frac{N}{C B(N)}.
$$
Because $\log t \le t/2$ for all $t \ge 2$, the terms in $\log B(N) = L_2(N) + L_3(N) + \cdots$ drop by at least a factor of $2$ each time, so $\log B(N) \le 2 L_2(N)$ for large $N$—hence $B(N) \le (\log N)^2$ and $x \to \infty$. Since $B$ is nondecreasing and $x \le N$, we have $C x B(x) \le C x B(N) = N$. Thus every denominator used is at most $N$, and $\log D \ge x = N/(C B(N))$, proving the theorem with $c = 1/C$. $\square$

The same estimate $\log B(t) \le 2 L_2(t)$ applied at $t = L_3(N)$ gives $B(L_3(N)) \le L_4(N)^2$. Since $B(N) = L_1(N) L_2(N) L_3(N) B(L_3(N))$, this exponent improves on the [four-stage construction](README.md#four-applications) by at least a constant multiple of $L_3(N) / L_4(N)^2$, which tends to infinity.
