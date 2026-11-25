# Order bounds for cubic bipartite counterexamples

**Theorem.** A nonempty finite simple cubic bipartite graph with no power-of-two cycle has at least **136 vertices**. If its number of perfect matchings is even, it has at least **150**.

Let $A,B$ be the two shores, each of size $m$. Let $M$ be the binary adjacency matrix with rows indexed by $B$ and columns by $A$. For a nonzero binary vector $z$, the number of ones in $Mz$ counts the rows that meet the support of $z$ oddly. We use the three bounds below. They follow by deleting an edge in each odd row and replacing every remaining two-edge path through an opposite vertex by a single edge. The resulting graph on the support of $z$ has respectively zero, one or two missing incidences. [Suppression lemma and odd-row bounds](AlgebraicDescent.md) · [Terminal searches](Bridges.md) · [Cubic bound, Theorem 5.1](https://arxiv.org/html/2609.28594v1#S5)

| Ones in $Mz$ | 0 | 1 | 2 |
|---|---:|---:|---:|
| Lower bound on the number of ones in $z$ | 50 | 41 | 32 |

**Proof.** Over $\mathbf F_2$ the determinant of $M$ is the parity of the number of perfect matchings. If it vanishes, take a nonzero $z$ in the kernel. Its support has size at least 50. Each selected vertex has three neighbors, and each of the $m$ opposite vertices sees at most two selected vertices. Thus $2m\ge3\cdot50=150$.

Otherwise write $Z=M^{-1}$ and let $z_i$ be its column indexed by $i\in B$. Every column of $Z$ has weight at least 41 by the table, as does every row since $Z^T=(M^T)^{-1}$. Every pair of columns has Hamming distance at least 32, since the sum of the columns maps to a vector with two ones. For the three neighbors $i,j,k$ of a vertex $x$ on the first shore, $ZM e_x=e_x$ says

$$z_i+z_j+z_k=e_x.$$

The distance between $z_i$ and $z_j$ is therefore at least $41-1=40$. Each $x$ supplies three such pairs and no pair repeats, since a repetition would give a 4-cycle.

Suppose $m\le67$. Count the total distance between all unordered pairs of columns, first by pairs and then by rows. Each of the $3m$ distinguished pairs contributes at least eight beyond the usual 32. A row of weight $r$ contributes $r(m-r)\le41(m-41)$, since $r\ge41>m/2$. Hence

$$
32\binom m2+24m\ \le\ \sum_{\text{rows}}r(m-r)\ \le\ 41m(m-41).
$$

Dividing by $m$ and rearranging gives $25m\ge1689$, contradicting $m\le67$. Thus $2m\ge136$.

## Bounds in terms of the terminal searches

Write $c,p,q$ for the order bounds with zero, one and two degree-two exceptions, as in the suppression lemma. In the singular case $2m\ge3c$. If the kernel has dimension $r$, its nonzero words all have weight at least $c$. The Griesmer bound gives

$$m\ge\sum_{i=0}^{r-1}\left\lceil c/2^i\right\rceil.$$

For a short proof, delete the support of a minimum-weight word of weight $h$. A nonzero word supported on those $h$ coordinates must use them all, so the kernel of this projection is the span of the chosen word. In each other coset, choose the representative occupying at most $\lfloor h/2\rfloor$ deleted coordinates. Its projection has weight at least $\lceil h/2\rceil$. Induction on the dimension gives the formula. Thus nullity at least three forces order at least 176, and nullity at least four forces order at least 190.

In the invertible case take $b=\min(q,p+1)$ and $d=\max(b,p-1)$. The same double count gives $b\binom m2+3m(d-b)\le mp(m-p)$ whenever $m<2p$. For $b<2p$ this gives

$$m\ge\min\left(2p,\left\lceil\frac{2p^2-b+6(d-b)}{2p-b}\right\rceil\right).$$

A single column always gives $2m\ge3p-1$ by the incidence count.

## Cubic graphs with a large independent set

Let an independent set $A$ in a cubic counterexample have size $a$ and its complement $B$ have size $b$. Set $t=b-a\ge0$, since all $3a$ edges incident to $A$ go to $B$. The cross-adjacency matrix $M$ now has $b$ rows and $a$ columns. A nonzero kernel word gives $2b\ge3c$, hence $|G|\ge3c-t$ as before.

Otherwise the image of $M$ has $2^t$ cosets. Distribute $0,e_1,\ldots,e_b$ among them. If $b\ge2^t$, two lie in the same coset. Their sum has a unique preimage whose weight is at least $h=\min(p,q)=32$. Counting its three incidences per selected vertex after at most two deletions gives $2b\ge3h-2=94$. For example, this excludes an 80-vertex cubic counterexample with an independent set of at least 38 vertices.

Choose $L\ge2$ of those vectors in a single coset and translate them by one of their members. Their preimages give $L$ binary words of length $a$ whose pairwise distances are all at least $h$. A coordinate containing $u$ ones contributes $u(L-u)$ to the total distance, so

$$
h\binom L2\ \le\ a\lfloor L^2/4\rfloor.
$$

Any $L\le\lceil(b+1)/2^t\rceil$ is available from a largest coset. In the coset containing zero, including zero gives the stronger lower bound $h\binom L2+(p-h)(L-1)$.

If $4\mid L$, equality would require $L/2$ ones in every coordinate. The sum of all preimages would vanish. Their images sum to the original $L$ vectors, since the translation is repeated an even number of times. This sum is nonzero, so the inequality is strict.

For $t=2,4$, the cubic bound $|G|\ge50$ ensures $b\ge2^t$. In the full-rank case the incidence count gives $b\ge47$. The kernel case has $|G|\ge150-t$. Two applications of the distance inequality complete the full-rank case.

| $t$ | First count | Second count | Order $2a+t$ |
|---:|---|---|---:|
| 2 | $L=12$ gives $a\ge59$, so $b\ge61$ | $L=16$ gives $64a>32\binom{16}{2}$, so $a\ge61$ | at least **124** |
| 4 | $L=3$ gives $a\ge48$, so $b\ge52$ | $L=4$ gives $4a>32\binom42$, so $a\ge49$ | at least **102** |

The 124-vertex bound applies to a cubic graph that becomes bipartite after deleting at most two edges. The bipartite case already has the bound 136. Otherwise take the coloring after deletion and write $e_A,e_B$ for its numbers of internal edges in the original graph. Degree counting gives $3(|A|-|B|)=2(e_A-e_B)$. Since $e_A+e_B\le2$ and at least one internal edge exists, there is exactly one in each equal shore. Omitting an endpoint of one such edge gives an independent set of size $|G|/2-1$, the case $t=2$.
