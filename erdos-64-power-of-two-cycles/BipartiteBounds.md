# Order bounds for cubic bipartite counterexamples

**Theorem.** Every nonempty finite simple cubic bipartite graph with no power-of-two cycle has at least **136 vertices**. If its number of perfect matchings is even, it has at least **150**.

Let $A, B$ be the two shores, each of size $m$, and let $M$ be the binary adjacency matrix with rows indexed by $B$ and columns by $A$. For a nonzero binary vector $z$, the ones in $Mz$ count the rows that meet the support of $z$ an odd number of times. Deleting one edge in each odd row and replacing every remaining two-edge path through $B$ by a single edge gives a graph on the support of $z$ with 0, 1, or 2 missing incidences. Combining the [suppression lemma](AlgebraicDescent.md) with the [terminal searches](Bridges.md) and the [cubic bound (Theorem 5.1)](https://arxiv.org/html/2609.28594v1#S5) gives the three lower bounds below.

| Ones in $Mz$ | 0 | 1 | 2 |
| --- | ---: | ---: | ---: |
| Lower bound on the number of ones in $z$ | 50 | 41 | 32 |

**Proof.** Over $\mathbf{F}_2$, the determinant of $M$ is the parity of the number of perfect matchings. If $\det M = 0$, pick a nonzero $z$ in the kernel of $M$. Its support has at least 50 vertices. Each selected vertex has three neighbors, and each of the $m$ vertices in $B$ sees at most two selected vertices, so $2m \ge 3 \cdot 50 = 150$.

Otherwise $M$ is invertible. Put $Z = M^{-1}$, and write $z_i$ for the column indexed by $i \in B$. Every column of $Z$ has weight at least 41 by the table, and every row has weight at least 41 because $Z^T = (M^T)^{-1}$. Any two columns are at Hamming distance at least 32, since their sum maps under $M$ to a vector with two ones. For any $x \in A$ with neighbors $i, j, k \in B$, the identity $ZM e_x = e_x$ reads

$$z_i + z_j + z_k = e_x.$$

Hence $z_i$ and $z_j$ have Hamming distance at least $41 - 1 = 40$. Each vertex $x \in A$ gives three such pairs, and no pair repeats because a repetition would form a 4-cycle.

Suppose $m \le 67$. Count the total Hamming distance across all unordered pairs of columns in two ways: by pairs and by rows. Each of the $3m$ special pairs adds at least 8 above the baseline 32. Each row of weight $r$ contributes $r(m - r) \le 41(m - 41)$, since $r \ge 41 > m/2$. Therefore

$$
32\binom{m}{2} + 24m \le \sum_{\text{rows}} r(m - r) \le 41m(m - 41).
$$

Dividing by $m$ and rearranging gives $25m \ge 1689$, contradicting $m \le 67$. Hence $2m \ge 136$.

## Bounds in terms of the terminal searches

Let $c, p, q$ be the order bounds for graphs with 0, 1, and 2 degree-two exceptions, as in the suppression lemma. In the singular case, $2m \ge 3c$. More generally, if the kernel of $M$ has dimension $r$, every nonzero word in it has weight at least $c$, and the Griesmer bound gives

$$m \ge \sum_{i=0}^{r-1} \left\lceil c / 2^i \right\rceil.$$

For a short proof, pick a minimum-weight nonzero word of weight $h$ and project onto the coordinates outside its support. Any nonzero word supported inside those $h$ coordinates must use all of them, so the kernel of this projection is the 1-dimensional span of the chosen word. In each other coset, pick the representative using at most $\lfloor h/2 \rfloor$ of the deleted coordinates; its projection has weight at least $\lceil h/2 \rceil$. Induction on $r$ gives the sum. With $c = 50$, nullity at least three forces order at least 176, and nullity at least four forces order at least 190.

In the invertible case, set $b = \min(q, p + 1)$ and $d = \max(b, p - 1)$. The same double count yields $b\binom{m}{2} + 3m(d - b) \le mp(m - p)$ whenever $m < 2p$. For $b < 2p$, this gives

$$m \ge \min\left(2p, \left\lceil \frac{2p^2 - b + 6(d - b)}{2p - b} \right\rceil\right).$$

Even a single column always gives $2m \ge 3p - 1$ by incidence counting.

## Cubic graphs with a large independent set

Suppose a cubic counterexample has an independent set $A$ of size $a$ and complement $B$ of size $b$. Set $t = b - a \ge 0$ (all $3a$ edges incident to $A$ go to $B$). The cross-adjacency matrix $M$ has $b$ rows and $a$ columns. If $M$ has a nonzero kernel word, then $2b \ge 3c$, so $|G| \ge 3c - t$ as before.

Otherwise $M$ has full column rank, and its image has $2^t$ cosets in $\mathbf{F}_2^b$. Place the $b + 1$ vectors $0, e_1, \ldots, e_b$ into these cosets. Whenever $b \ge 2^t$, two of them share a coset. Their sum has a unique preimage of weight at least $h = \min(p, q) = 32$. Counting its three edges per selected vertex after at most two deletions gives $2b \ge 3h - 2 = 94$. For instance, this rules out an 80-vertex cubic counterexample containing an independent set of size at least 38.

Pick $L \ge 2$ of those vectors from one coset and shift them by one of their members. Their preimages are $L$ binary words of length $a$ with pairwise Hamming distance at least $h$. A coordinate containing $u$ ones contributes $u(L - u)$ to the total pairwise distance, so

$$
h\binom{L}{2} \le a\lfloor L^2 / 4 \rfloor.
$$

Any $L \le \lceil (b + 1) / 2^t \rceil$ is available in a largest coset. In the coset containing 0, including 0 raises the left side to $h\binom{L}{2} + (p - h)(L - 1)$.

When $4 \mid L$, this inequality is strict. Equality would force $L/2$ ones in every coordinate, so the sum of all $L$ preimages would be zero. Their images under $M$, however, sum to the original $L$ distinct vectors (since the shift appears an even number of times), which cannot be zero.

For $t = 2$ and $t = 4$, the cubic bound $|G| \ge 50$ guarantees $b \ge 2^t$. In the full-rank case, incidence counting gives $b \ge 47$; the kernel case already gives $|G| \ge 150 - t$. Two rounds of the distance bound finish the full-rank case:

| $t$ | First count | Second count | Order $2a + t$ |
| ---: | --- | --- | ---: |
| 2 | $L = 12$ gives $a \ge 59$, so $b \ge 61$ | $L = 16$ gives $64a > 32\binom{16}{2}$, so $a \ge 61$ | at least **124** |
| 4 | $L = 3$ gives $a \ge 48$, so $b \ge 52$ | $L = 4$ gives $4a > 32\binom{4}{2}$, so $a \ge 49$ | at least **102** |

The 124-vertex bound also covers any cubic counterexample that becomes bipartite after deleting at most two edges. If it is already bipartite, the bound 136 applies. Otherwise take the 2-coloring after deletion and let $e_A, e_B$ count its internal edges in the original graph. Counting degrees gives $3(|A| - |B|) = 2(e_A - e_B)$. Since $1 \le e_A + e_B \le 2$, the only solution has $|A| = |B|$ and $e_A = e_B = 1$. Dropping one endpoint of an internal edge leaves an independent set of size $|G|/2 - 1$, which is the case $t = 2$.
