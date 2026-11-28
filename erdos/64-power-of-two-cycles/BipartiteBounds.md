# Order Bounds for Cubic Bipartite Counterexamples

How small can a cubic *bipartite* counterexample to Erdős Problem #64 be? We already know from [AlgebraicDescent.md](AlgebraicDescent.md) that no smallest cubic counterexample is bipartite. By turning the suppression lemma into a coding-theory style distance bound on the binary adjacency matrix $M$ (and its inverse $M^{-1}$ over $\mathbf{F}_2$), we can push the minimum order of a cubic bipartite counterexample far past the general 50-vertex cubic bound.

**Theorem.** Every nonempty finite simple cubic bipartite graph with no power-of-two cycle has at least **136 vertices**. If its number of perfect matchings is even, it has at least **150 vertices**.

The same $\mathbf{F}_2$ method also bounds nonbipartite cubic counterexamples that contain a large independent set, forcing at least **124 vertices** when an independent set comes within one vertex of half the graph (including any cubic counterexample made bipartite by deleting at most two edges) and at least **102 vertices** when it comes within two vertices.

---

## Setup: turning neighborhoods into binary codes

Let $G$ be a finite simple cubic bipartite graph with no power-of-two cycle. Its two independent *shores* $A$ and $B$ have the same size $m$ (so $|G| = 2m$). Let $M$ be the $m \times m$ binary adjacency matrix over $\mathbf{F}_2$ with rows indexed by $B$ and columns indexed by $A$.

For any nonzero binary vector $z \in \mathbf{F}_2^m$, identify $z$ with its support $X \subseteq A$. The $1$-entries of $Mz$ count the rows in $B$ that see an odd number ($1$ or $3$) of vertices of $X$. As proved in [AlgebraicDescent.md](AlgebraicDescent.md), deleting one edge in each odd row and replacing every remaining two-edge path through $B$ by a single edge yields a dyadic-cycle-free graph on $X$ that is cubic except for at most $|Mz|$ missing incidences. Combining the [suppression lemma](AlgebraicDescent.md) with the [terminal searches](Bridges.md) ($p = 41$, $q = 32$) and the [cubic bound (Theorem 5.1)](https://arxiv.org/html/2609.28594v1#S5) ($c = 50$) gives three lower bounds on the Hamming weight $|z|$ (the number of $1$s in $z$):

| Ones in $Mz$ | 0 | 1 | 2 |
| --- | ---: | ---: | ---: |
| Lower bound on the number of ones in $z$ | 50 | 41 | 32 |

---

## Proof of the 136- and 150-vertex bounds

**The big idea.** Over $\mathbf{F}_2$, the determinant $\det M$ equals the number of perfect matchings of $G$ modulo $2$ (each permutation term in the Leibniz expansion is $1$ exactly when it picks a perfect matching).
* When $\det M = 0$, a single nonzero kernel vector already forces $2m \ge 150$ by counting edges.
* When $\det M = 1$, every column and every row of $Z = M^{-1}$ has weight at least $41$, every pair of columns is at Hamming distance at least $32$, and the absence of $4$-cycles hands us $3m$ *special* pairs of columns at distance at least $40$. Double-counting total pairwise Hamming distance across the $m$ columns forces $m \ge 68$.

**Proof.**

### Case 1: $\det M = 0$ (even number of perfect matchings)

Pick a nonzero vector $z \in \ker M$. By the table above, its support $X \subseteq A$ has size $|X| \ge 50$. Each vertex of $X$ sends $3$ edges to $B$, and every vertex of $B$ sees an even number of vertices of $X$ — hence at most $2$, since $G$ is cubic. Counting edges between $X$ and $B$ gives

$$
2m \ge 3|X| \ge 3 \cdot 50 = 150.
$$

### Case 2: $\det M = 1$ (invertible $M$)

Put $Z = M^{-1}$, and write $z_i$ for the column of $Z$ indexed by $i \in B$. Three distance facts hold:

1. **Row and column weights $\ge 41$:** Since $M z_i = e_i$ has weight $1$, every column $z_i$ has weight at least $41$. Because $Z^T = (M^T)^{-1}$ and $M^T$ is just the adjacency matrix with $A$ and $B$ swapped, every row of $Z$ also has weight at least $41$.
2. **Baseline pairwise distance $\ge 32$:** For any distinct $i, j \in B$, the sum $z_i + z_j$ maps under $M$ to $e_i + e_j$ (weight $2$), so the Hamming distance between $z_i$ and $z_j$ is $|z_i + z_j| \ge 32$.
3. **$3m$ special pairs at distance $\ge 40$:** Pick any $x \in A$, and let $i, j, k \in B$ be its three neighbors. The $x$-th column of $M$ is $e_i + e_j + e_k$, so the identity $ZM e_x = e_x$ reads
   $$
   z_i + z_j + z_k = e_x.
   $$
   Rearranging to $z_i + z_j = z_k + e_x$ shows that $z_i$ and $z_j$ differ in at least $|z_k| - 1 \ge 41 - 1 = 40$ coordinates — at least $8$ above the baseline $32$. Each vertex $x \in A$ contributes three such pairs ($\{i, j\}, \{i, k\}, \{j, k\}$), and no pair can be produced by two different vertices $x, x' \in A$, because two vertices sharing two neighbors would form a $4$-cycle.

Now suppose for contradiction that $m \le 67$, and count the sum of Hamming distances over all $\binom{m}{2}$ unordered pairs of columns of $Z$ in two ways:

* **Lower bound (by pairs):** Each of the $\binom{m}{2}$ pairs contributes at least $32$, and each of the $3m$ distinct special pairs adds a bonus of at least $8$, for at least $32\binom{m}{2} + 24m$.
* **Upper bound (by rows):** A row of weight $r$ has $r$ ones and $m - r$ zeros, so it contributes $r(m - r)$ to the total pairwise Hamming distance. Since $r \ge 41 > 67/2 \ge m/2$, the function $r(m - r)$ decreases as $r$ grows, so every row contributes at most $41(m - 41)$.

Combining the two counts gives

$$
32\binom{m}{2} + 24m \le \sum_{\text{rows}} r(m - r) \le 41m(m - 41).
$$

Dividing through by $m$ yields $16(m - 1) + 24 \le 41m - 1681$, which simplifies to $25m \ge 1689$. Since $25 \cdot 67 = 1675 < 1689$, this contradicts $m \le 67$. Therefore $m \ge 68$ and $2m \ge 136$. $\square$

---

## General bounds in terms of the terminal searches

The proof above works for any positive integer lower bounds $c, p, q$ on connected dyadic-cycle-free graphs with $0, 1,$ and $2$ degree-two exceptions (as in the suppression lemma).

### Higher-dimensional kernels (Griesmer bound)

In the singular case, a single kernel vector gives $2m \ge 3c$. More generally, if $\ker M$ has dimension $r$ over $\mathbf{F}_2$, then $\ker M$ is an $[m, r, \ge c]$ binary linear code, so the **Griesmer bound** forces

$$
m \ge \sum_{i=0}^{r-1} \left\lceil c / 2^i \right\rceil.
$$

**Short self-contained proof.** Pick a minimum-weight nonzero codeword $w \in \ker M$ of weight $h \ge c$, and project $\ker M$ onto the $m - h$ coordinates outside the support of $w$. Any nonzero codeword supported inside those $h$ coordinates must use all of them (by minimality of $h$), so the kernel of this projection is the $1$-dimensional span $\{0, w\}$. In every other coset $\{u, u + w\}$, pick the representative that puts at most $\lfloor h/2 \rfloor$ ones inside the deleted $h$ coordinates; since its total weight is at least $h$, its projection onto the remaining $m - h$ coordinates has weight at least $h - \lfloor h/2 \rfloor = \lceil h/2 \rceil \ge \lceil c/2 \rceil$. Induction on $r$ produces the sum.

With $c = 50$:
* Nullity $r \ge 3$ gives $m \ge 50 + 25 + 13 = 88$, forcing order at least **176**.
* Nullity $r \ge 4$ gives $m \ge 50 + 25 + 13 + 7 = 95$, forcing order at least **190**.

### General invertible bound

In the invertible case, set $b = \min(q, p + 1)$ and $d = \max(b, p - 1)$. Whenever $m < 2p$, the exact same double count gives $b\binom{m}{2} + 3m(d - b) \le mp(m - p)$. For $b < 2p$, rearranging yields

$$
m \ge \min\left(2p, \left\lceil \frac{2p^2 - b + 6(d - b)}{2p - b} \right\rceil\right).
$$

Even a single column of $Z$ always gives the incidence bound $2m \ge 3p - 1$.

---

## Cubic graphs with a large independent set

Now drop the bipartiteness assumption and suppose a cubic counterexample $G$ merely contains a large independent set $A$ of size $a$, with complement $B$ of size $b$. Because all $3a$ edges incident to $A$ cross into $B$ (and $B$ has at most $3b$ total incidences), we have $b \ge a$. Set the excess $t = b - a \ge 0$, so $|G| = a + b = 2a + t$.

Let $M$ be the $b \times a$ cross-adjacency matrix over $\mathbf{F}_2$ (rows indexed by $B$, columns by $A$).

* **Kernel case:** If $M$ has a nonzero kernel vector, the same edge count as before gives $2b \ge 3c$, hence $|G| = 2b - t \ge 3c - t$ (at least $150 - t$ for $c = 50$).
* **Full-column-rank case:** Otherwise $M$ is injective, so its image $\operatorname{im}(M)$ is an $a$-dimensional subspace of $\mathbf{F}_2^b$ with $2^{b - a} = 2^t$ cosets.

### Coset pigeonhole and Plotkin-style distance bound

Place the $b + 1$ vectors $0, e_1, \ldots, e_b \in \mathbf{F}_2^b$ into the $2^t$ cosets of $\operatorname{im}(M)$. Whenever $b \ge 2^t$, some coset holds at least two of these vectors. Their sum belongs to $\operatorname{im}(M)$ and has weight $1$ or $2$, so its unique preimage in $\mathbf{F}_2^a$ has weight at least $h = \min(p, q) = 32$. Counting its $3$ incident edges per selected vertex after deleting at most $2$ edges gives

$$
2b \ge 3h - 2 = 94 \implies b \ge 47.
$$

For instance, this immediately rules out an $80$-vertex cubic counterexample containing an independent set of size $a \ge 38$: we have $b = 80 - a \le 42$ and $t = b - a \le 4$, so $b \ge 16 \ge 2^t$, which forces either $|G| \ge 150 - 4 = 146$ (kernel case) or $b \ge 47$ (full-rank case).

To push the full-rank bound even higher, pick $L \ge 2$ of the vectors $0, e_1, \ldots, e_b$ lying in a single coset, and shift all $L$ of them by adding one of their members. All $L$ shifted vectors lie in $\operatorname{im}(M)$, and any two differ by a vector of weight $1$ or $2$, so their preimages form $L$ binary words of length $a$ at pairwise Hamming distance at least $h$. In each of the $a$ coordinates, if $u$ words have a $1$ and $L - u$ have a $0$, that coordinate contributes $u(L - u) \le \lfloor L^2 / 4 \rfloor$ to the total pairwise Hamming distance. Summing over coordinates gives the Plotkin-type inequality

$$
h\binom{L}{2} \le a\lfloor L^2 / 4 \rfloor.
$$

Two refinements sharpen this inequality:
* **Choosing $L$:** By averaging over the $2^t$ cosets, a largest coset contains at least $\lceil (b + 1) / 2^t \rceil$ of our $b + 1$ vectors, so any $L \le \lceil (b + 1) / 2^t \rceil$ is available. In the coset containing $0$, including $0$ raises the $L - 1$ distances from $0$ to at least $p$, lifting the left-hand side to $h\binom{L}{2} + (p - h)(L - 1)$.
* **Strict inequality when $4 \mid L$:** When $L$ is a multiple of $4$, equality in $h\binom{L}{2} \le a(L^2 / 4)$ is impossible. Equality would force $u = L/2$ ones in every coordinate; since $L/2$ is even, the sum of all $L$ preimages would be $0$ over $\mathbf{F}_2$, so their images under $M$ would also sum to $0$. Yet each image is one of our $L$ distinct vectors from $\{0, e_1, \ldots, e_b\}$ plus the fixed shift; because $L$ is even, the shift cancels out, leaving the sum of $L$ distinct vectors from $\{0, e_1, \ldots, e_b\}$ — which has weight $L$ or $L - 1 \ge 3$ and cannot be zero.

### Bootstrapping $t = 2$ and $t = 4$

For $t = 2$ and $t = 4$, the cubic bound $|G| \ge 50$ guarantees $b \ge 26 \ge 2^t$. In the kernel case we already get $|G| \ge 150 - t$. In the full-rank case, incidence counting starts us at $b \ge 47$, and two rounds of the distance bound bootstrap the order:

| $t$ | First round | Second round | Order $2a + t$ |
| ---: | --- | --- | ---: |
| 2 | $b \ge 47 \implies L = 12$ available; $36a > 32\binom{12}{2}$ gives $a \ge 59$, so $b \ge 61$ | $L = 16$ available; $64a > 32\binom{16}{2}$ gives $a \ge 61$ | at least **124** |
| 4 | $b \ge 47 \implies L = 3$ available; $2a \ge 32\binom{3}{2}$ gives $a \ge 48$, so $b \ge 52$ | $L = 4$ available; $4a > 32\binom{4}{2}$ gives $a \ge 49$ | at least **102** |

### Near-bipartite cubic counterexamples

The **124-vertex** bound also covers **any cubic counterexample that becomes bipartite after deleting at most two edges**.

If the graph is already bipartite, the $136$-vertex bound applies. Otherwise, take the $2$-coloring $(A, B)$ after deleting those edges, and let $e_A, e_B$ count the internal edges inside $A$ and $B$ in the original cubic graph. Counting edges crossing between $A$ and $B$ from both sides gives

$$
3|A| - 2e_A = 3|B| - 2e_B \implies 3(|A| - |B|) = 2(e_A - e_B).
$$

Because $1 \le e_A + e_B \le 2$, the difference $|e_A - e_B|$ is $0, 1,$ or $2$. The only multiple of $3$ among them is $0$, which forces $|A| = |B|$ and $e_A = e_B = 1$. Removing one endpoint of the single internal edge in $A$ leaves an independent set of size $|G|/2 - 1$, which puts us directly in the case $t = 2$.
