# One congruence per prime determines the gap

Let $L=\operatorname{lcm}(1,\ldots,N)$. For each prime $p\le N$, let $q_p$ be its largest power at most $N$. Let $C_p$ be the set of subset sums modulo $p$ of the integer list
$$
\frac{L}{q_p},\quad \frac{L}{2q_p},\quad\ldots,\quad
\frac{L}{\lfloor N/q_p\rfloor q_p}.
$$

**Theorem.** For all sufficiently large $N$ and every integer $h$ with $|h|\le L/2$, the number $1+h/L$ is a sum of distinct reciprocals with denominators at most $N$ if and only if $h\bmod p\in C_p$ for every prime $p\le N$. In particular $L\delta(N)$ is the least nonzero $|h|$ passing these tests.

**Necessity.** Multiply the sum by $L$. Modulo $p$, the terms $L/n$ vanish except when $q_p\mid n$. The surviving terms are exactly the displayed list. For $p>N/2$, for example, the two possible residues are $0$ and $L/p$.

**Sufficiency.** Put $S=cN/((\log N)^3(\log\log N)^4)$ for a sufficiently small constant $c>0$, and $Q=\operatorname{lcm}(1,\ldots,\lfloor S\rfloor)$. We use two facts. Denominators $n\le N$ outside the divisors of $Q$ have total reciprocal sum $o(1)$. Every rational in $[1/3,3/2]$ whose denominator divides $Q$ can be represented using distinct divisors of $Q$ at most $N$. For the second fact, Liu and Sawhney's Lemma 4.1 and its proof cover $[1/3,1]$ using denominators in $[N/16,N]$. Above 1, first set aside $1/2$. [Estimate for the first fact](README.md#an-exact-reduction-for-the-target-1) · [Liu and Sawhney, §4](https://arxiv.org/html/2404.07113v1#S4)

Start with $t=1+h/L$. Repeatedly take the largest prime power $q=p^v>S$ dividing the reduced denominator of the current remainder $t$. In $qt$, the denominator is prime to $p$, so $qt\bmod p$ is defined. To remove a factor of $p$, subtract terms $1/(qj)$ whose $j^{-1}$ sum to this residue modulo $p$.

* If $q=q_p$, the assumed test supplies these terms. Indeed, initially $q_pt\equiv h/(L/q_p)\pmod p$. Earlier terms leave this residue unchanged because each earlier denominator already contains a different prime power above $S>\sqrt N$ and cannot also contain $q_p$.
* If $q<q_p$, one term suffices. Choose $1\le j<p$ with $j^{-1}\equiv qt\pmod p$. The residue is nonzero since $q$ is the exact power of $p$ in the reduced denominator, and $qj<pq\le N$.

In both cases $j<p\le q$. Subtraction removes $q$ from the denominator and can introduce only prime powers dividing a cofactor $j$. All are smaller than $q$, so the largest power above $S$ strictly decreases. Every chosen denominator has $q$ as its largest prime-power divisor, ensuring distinctness between steps.

When the process stops, the denominator divides $Q$. The total subtracted is $o(1)$ by the first fact, so the remainder lies in $[1/3,3/2]$. The second fact fills it using divisors of $Q$, disjoint from all earlier terms. Finally $1+1/N$ is attainable, so a nonzero passing $|h|\le L/N$ already lies in the theorem's interval. This proves the minimum formula.

<details>
<summary>An elementary proof of the representation fact using the first grid construction</summary>

For each prime $p$, every residue modulo $p$ has a representation $\sum_{j\in J}1/j$ with distinct $j<p$, with $j\ll(1+\log p)^3$ and total reciprocal sum $\ll1/(1+\log p)$. To see this for large $p$, use the [first grid construction](README.md#four-applications) at $x=6\log p$. It represents every $m/D\in[1/8,1]$ with $D\ge p^2$ and denominators $d\ll(\log p)^2$ dividing $D$. Put $T=\lceil\log p\rceil$. The consecutive numerators $m$ cover all residues modulo $p$, and $p\nmid TD$ since the prime factors of $D$ are at most $x<p$. Thus the fractions $m/(TD)$ also cover all residues. Their denominators in the representation are $j=Td<p$ and their sums are at most $1/T$. For the finitely many small primes a single inverse or the empty sum suffices after enlarging the constants.

Now take any target in $[1/3,3/2]$ with denominator dividing $Q$. For each successive largest prime power $q=p^v>K$ in its denominator, apply this residue representation to $q$ times the current remainder and subtract the terms $1/(qj)$. As above, the largest power decreases, and all chosen denominators are distinct. Each $qj$ divides $Q$ because $j<p\le q\le S$, and $qj\ll S(1+\log N)^3\le N$ for large $N$. The total cost is at most a constant times
$$
\sum_{p^v>K}\frac{1}{p^v(1+\log p)}.
$$
This tail tends to zero. Summing over $v$ gives a convergent full series since $\sum_p 1/(p\log p)<\infty$ by dyadic summation and $\pi(x)\ll x/\log x$. Fix $K\ge2$ large enough that the total cost is below $1/3$.

The remainder is $m/D_0\in[0,3/2]$, where $D_0=\operatorname{lcm}(1,\ldots,K)$ is fixed and eventually below $N$. Write $D_0=2^a p_1\cdots p_s$ with odd primes listed with multiplicity. Divide $m$ successively by $p_1,\ldots,p_s$. Each remainder is less than $p_i\le K<2^{a+1}$, and the final quotient is at most $3\cdot 2^{a-1}<2^{a+1}$. Expanding each of these digits in binary expresses $m$ as a sum of distinct divisors $2^j p_1\cdots p_i$ of $D_0$, with $0\le j\le a$ and the empty prefix allowed. Dividing by $D_0$ gives the required reciprocals. Their denominators divide $D_0$, so they are disjoint from every previous step.

</details>

## The remaining arithmetic question

The tests specify residue classes modulo $M=\prod_{p:\,C_p\ne\mathbb F_p}p$. Since $\log L=N+o(N)$, problem #311 asks whether the logarithm of the least nonzero passing magnitude is $(1-c+o(1))N$ for some fixed $c\in(0,1)$. The quotient $L/M$ is the largest denominator of a complete grid in $[1/2,3/2]$. [Original problem](https://www.erdosproblems.com/311) · [Largest-grid proof](largest-grid.md)
