# One congruence per prime determines the gap

Can you decide whether a target fraction near $1$ is a sum of distinct unit fractions $1/n$ ($n \le N$) by checking one simple modular congruence for each prime $p \le N$? Clearing denominators by $L = \operatorname{lcm}(1, \ldots, N)$ makes one modular condition per prime obviously *necessary*. The theorem proved here shows that for all sufficiently large $N$, those local prime congruences are also *completely sufficient* throughout the interval $[1/2, 3/2]$.

## Setup and main theorem

Let $L = \operatorname{lcm}(1, \ldots, N)$. For each prime $p \le N$:
* Let $q_p$ be the largest power of $p$ satisfying $q_p \le N$ (so $q_p$ is the exact power of $p$ dividing $L$).
* Let $C_p \subseteq \mathbb{F}_p$ be the set of all subset sums modulo $p$ of the integer list
  $$
  \frac{L}{q_p}, \quad \frac{L}{2q_p}, \quad \ldots, \quad \frac{L}{\lfloor N/q_p \rfloor q_p}.
  $$
  (The empty sum $0 \bmod p$ is always included in $C_p$.)

*Sanity check.* If $p > N/2$, then $q_p = p$ and $\lfloor N/p \rfloor = 1$, so the list has only one element $L/p$ and $C_p = \{0, L/p\} \bmod p$. For example, at $N = 4$ we have $L = 12$, $q_3 = 3$, and $C_3 = \{0, 4\} \equiv \{0, 1\} \pmod 3$: indeed $13/12 = 1 + 1/12$ ($h = 1 \in C_3$) is attainable as $1/2 + 1/3 + 1/4$, whereas $11/12 = 1 - 1/12$ ($h = -1 \equiv 2 \notin C_3$) is impossible.

**Theorem (Prime residue criterion).** For all sufficiently large $N$ and every integer $h$ with $|h| \le L/2$, the rational number $1 + h/L$ is a sum of distinct reciprocals with denominators at most $N$ if and only if
$$
h \bmod p \in C_p \qquad \text{for every prime } p \le N.
$$
In particular, $L \delta(N)$ is the least nonzero $|h|$ passing all of these prime tests.

---

## Proof of necessity

Suppose $1 + h/L = \sum_{n \in A} 1/n$ for some subset $A \subseteq \{1, \ldots, N\}$. Multiply both sides by $L$:
$$
L + h = \sum_{n \in A} \frac{L}{n}.
$$
Now reduce modulo a prime $p \le N$. Since $p \mid L$, the left-hand side reduces to $h \bmod p$. On the right-hand side, $q_p$ is the exact power of $p$ dividing $L$, so $L/n$ is divisible by $p$ unless $q_p \mid n$. The only denominators $n \le N$ divisible by $q_p$ are $q_p, 2q_p, \ldots, \lfloor N/q_p \rfloor q_p$, whose contributions $L/n$ are precisely the displayed list. Therefore $h \bmod p \in C_p$. (For $p > N/2$, this recovers the two allowed residues $0$ and $L/p$.)

---

## Proof of sufficiency

**The big idea (top-down prime-power peeling).** Set a smooth cutoff $S$ well below $N$ and let $Q = \operatorname{lcm}(1, \ldots, \lfloor S \rfloor)$. Starting from the target $t = 1 + h/L$, we repeatedly find the *largest* prime power $q = p^v > S$ dividing the reduced denominator of our current remainder $t$, and subtract one or more fractions $1/(qj)$ (with $j < p \le q$) chosen to cancel $p$ modulo $q$. Because every cofactor $j$ is strictly smaller than $q$, this strictly lowers the largest prime power above $S$ in the denominator, and because every chosen denominator has $q$ as its unique largest prime-power divisor, no denominator is ever reused. Once all prime powers above $S$ are gone, the remainder's denominator divides $Q$, very little total mass ($o(1)$) has been subtracted, and a complete grid over divisors of $Q$ finishes the representation.

### Two ingredients

Set
$$
S = \frac{cN}{(\log N)^3 (\log\log N)^4}
$$
for a sufficiently small constant $c > 0$, and put $Q = \operatorname{lcm}(1, \ldots, \lfloor S \rfloor)$. We rely on two facts:

1. **Rough reciprocals have tiny sum:** The denominators $n \le N$ that do not divide $Q$ have total reciprocal sum $o(1)$. [Estimate for the first fact](README.md#an-exact-reduction-for-the-target-1)
2. **Smooth complete grid:** Every rational in $[1/3, 3/2]$ whose denominator divides $Q$ can be represented as a sum of distinct divisors of $Q$ at most $N$. For $[1/3, 1]$, this follows from Liu and Sawhney's Lemma 4.1 and its proof (which uses denominators in $[N/16, N]$); for targets in $(1, 3/2]$, simply set aside the denominator $2$ (i.e., subtract $1/2$) first, noting $2 < N/16$. An entirely elementary proof using our first grid construction is also given in the collapsible box below. [Liu and Sawhney, §4](https://arxiv.org/html/2404.07113v1#S4)

### Peeling off prime powers above $S$

Initialize $t = 1 + h/L \in [1/2, 3/2]$. While the reduced denominator of $t$ is divisible by some prime power larger than $S$, let $q = p^v > S$ be the **largest** prime power dividing the reduced denominator of $t$.

Because $q$ is the exact power of $p$ in the reduced denominator of $t$, the product $qt$ has denominator coprime to $p$, so the residue $qt \bmod p$ is well-defined and nonzero. To clear a factor of $p$ from the denominator of $t$, we subtract a sum $\sum_{j \in J} 1/(qj)$ whose modular inverses $\sum_{j \in J} j^{-1} \bmod p$ match $qt \bmod p$. There are two cases:

* **Case 1: $q = q_p$ (maximal power of $p$ up to $N$).** Initially, for $t_0 = 1 + h/L$, we have
  $$
  q_p t_0 = q_p + \frac{h}{L/q_p} \equiv \frac{h}{L/q_p} \pmod p.
  $$
  Did any earlier peeling step alter $q_p t \bmod p$? No! Each earlier step used denominators of the form $q' j'$ with $q' > q > S > \sqrt{N}$. Because $q' > \sqrt{N}$ and $q_p > \sqrt{N}$ are powers of distinct primes (we process prime powers in strictly decreasing order, and $q_p$ is the *highest* power of $p$), their product $q' q_p > N$, so no earlier denominator $q' j' \le N$ could be divisible by $q_p$. Thus $q_p t \equiv h (L/q_p)^{-1} \pmod p$ still holds untouched. By the hypothesis $h \bmod p \in C_p$, there is a subset $J \subseteq \{1, \ldots, \lfloor N/q_p \rfloor\}$ with $\sum_{j \in J} (L/(j q_p)) \equiv h \pmod p$, i.e., $\sum_{j \in J} j^{-1} \equiv q_p t \pmod p$.
* **Case 2: $q < q_p$ (a smaller power of $p$ than the maximum $q_p$).** Here $pq \le q_p \le N$, so a *single* term suffices! Since $qt \not\equiv 0 \pmod p$, pick the unique $1 \le j < p$ with $j^{-1} \equiv qt \pmod p$, and subtract $1/(qj)$. Its denominator satisfies $qj < pq \le N$.

Let us check termination and distinctness:
* In both cases, every cofactor $j$ satisfies $j < p \le q$ (in Case 1, $\lfloor N/q_p \rfloor < p$ by maximality of $q_p$).
* Subtracting $\sum_{j \in J} 1/(qj)$ eliminates $q$ from the denominator of $t$ (reducing the $p$-adic valuation by at least $1$) and can only introduce prime powers dividing some $j$, all of which are strictly less than $q$. Thus the largest prime power above $S$ in the reduced denominator strictly decreases at every step, so the loop terminates.
* Every denominator $qj$ chosen at step $q$ has $q$ as its unique largest prime-power divisor (since $j < q$). Different steps have different values of $q$, so denominators from different steps are guaranteed to be distinct, and within a step the $j \in J$ are distinct.

### Finishing on the smooth grid and deducing the minimum formula

When the peeling loop terminates, every prime power dividing the reduced denominator of the remaining $t$ is at most $S$, so the denominator divides $Q$. Every denominator used during peeling was divisible by some $q > S$ and hence does not divide $Q$; by Fact 1, the total mass subtracted is $o(1)$. Since we started in $[1/2, 3/2]$, the final remainder lies in $[1/3, 3/2]$ for all sufficiently large $N$. Fact 2 represents this remainder using distinct divisors of $Q$ at most $N$—automatically disjoint from all denominators used in peeling.

Finally, $1 + 1/N$ is always attainable (take $\{1, N\}$), so $\delta(N) \le 1/N$ and the least nonzero passing $|h|$ satisfies $|h| \le L/N \le L/2$, which lies inside the theorem's range. This proves the exact formula for $L \delta(N)$. $\square$

<details>
<summary>An elementary proof of the smooth-grid representation fact (Fact 2) using the first grid construction</summary>

We can prove Fact 2 without invoking Liu and Sawhney's Lemma 4.1, using only our elementary [first grid construction](README.md#four-applications).

**Step 1: Cheap modulo-$p$ residue covering.** We claim that for every prime $p$, every residue modulo $p$ can be written as $\sum_{j \in J} 1/j \pmod p$ using distinct $j < p$ with
$$
j \ll (1 + \log p)^3 \qquad \text{and} \qquad \sum_{j \in J} \frac{1}{j} \ll \frac{1}{1 + \log p}.
$$
To see this for large $p$, run the [first grid construction](README.md#four-applications) at scale $x = 6 \log p$. It gives a denominator $D \ge e^{x/3} = p^2$, with all prime factors at most $x < p$, such that every $m/D \in [1/8, 1]$ is representable using distinct divisors $d \mid D$ with $d \ll (\log p)^2$. Put $T = \lceil \log p \rceil$. Since $D > 2p$, the numerators $m \in [D/8, D]$ cover all residues modulo $p$, and $p \nmid TD$ for large $p$. Scaling all denominators by $T$ gives fractions $m/(TD)$ that still cover all residues modulo $p$, use distinct denominators $j = Td \ll (\log p)^3 < p$, and have total reciprocal sum $m/(TD) \le 1/T$. For the finitely many small primes, a single modular inverse (or the empty sum for $0$) suffices after enlarging the implied constants.

**Step 2: Peel smooth prime powers down to a fixed cutoff $K$.** Given any target in $[1/3, 3/2]$ whose denominator divides $Q$, repeatedly pick the largest prime power $q = p^v > K$ dividing the reduced denominator of the current remainder, represent $q$ times the remainder modulo $p$ using Step 1, and subtract $\sum_{j \in J} 1/(qj)$. Just as before, the largest prime power strictly decreases and all chosen denominators are distinct. Every chosen $qj$ divides $Q$ because $j < p \le q \le S$ (so every prime power dividing $qj$ is at most $S$), and $qj \ll S (1 + \log N)^3 \le N$ for large $N$. The total reciprocal sum subtracted is at most a constant times
$$
\sum_{p^v > K} \frac{1}{p^v (1 + \log p)}.
$$
Summing over $v \ge 1$ gives a convergent series because $\sum_p 1/(p \log p) < \infty$ (by dyadic summation and $\pi(x) \ll x/\log x$). Fix a constant $K \ge 2$ large enough that this tail cost is strictly less than $1/3$.

**Step 3: Exact representation for the fixed base denominator $D_0$.** Once no prime power above $K$ remains, we are left with $m/D_0 \in [0, 3/2]$, where $D_0 = \operatorname{lcm}(1, \ldots, K)$ is a fixed constant (eventually $\le N$). Factor $D_0 = 2^a p_1 \cdots p_s$ with odd primes listed with multiplicity. Repeatedly divide $m$ by $p_1, \ldots, p_s$ with remainder:
* Each remainder $r_i$ satisfies $0 \le r_i < p_i \le K < 2^{a+1}$ (since $2^a$ is the largest power of $2$ at most $K$, so $2^{a+1} > K$).
* The final quotient $q_s$ satisfies $0 \le q_s = \lfloor m / (p_1 \cdots p_s) \rfloor \le \lfloor \frac{3}{2} \cdot 2^a \rfloor < 2^{a+1}$.

Thus $m = r_1 + r_2 p_1 + \cdots + r_s (p_1 \cdots p_{s-1}) + q_s (p_1 \cdots p_s)$. Expanding each digit $r_i$ and $q_s$ in binary (using powers $2^j$ with $0 \le j \le a$) expresses $m$ as a sum of distinct divisors $2^j p_1 \cdots p_i$ of $D_0$ (allowing the empty product for $i = 0$). Dividing by $D_0$ produces distinct unit fractions whose denominators divide $D_0$, hence are disjoint from every denominator chosen in Step 2 (each of which was divisible by a prime power $> K$).

</details>

---

## The remaining arithmetic question

Collect the primes where the modular test is actually nontrivial (i.e., not every residue is allowed) into the modulus
$$
M = \prod_{\substack{p \le N \\ C_p \ne \mathbb{F}_p}} p.
$$
By the theorem, $L \delta(N)$ is the smallest positive magnitude $|h|$ falling in the allowed residue classes modulo $M$. Because $\log L = N + o(N)$, Erdős Problem #311 is equivalent to asking whether the logarithm of this least nonzero passing $|h|$ satisfies
$$
\log \bigl(L \delta(N)\bigr) = (1 - c + o(1)) N
$$
for some fixed constant $c \in (0, 1)$. Meanwhile, the complementary factor $L/M$ turns out to be *exactly* the largest denominator of a complete grid on $[1/2, 3/2]$. [Original problem](https://www.erdosproblems.com/311) · [Largest-grid proof](largest-grid.md)
