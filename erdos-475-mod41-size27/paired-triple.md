# Graham orderings with at most three omitted residues

This note proves that at **every prime $p$**, any subset of the nonzero residues omitting at most three elements has a valid Graham ordering.

**Theorem.** At every prime $p$, any $A \subseteq \mathbb{F}_p^\times$ that omits at most three nonzero residues has an ordering with distinct nonempty partial sums.

> **Note:** A newer [unified proof](paired-quartet.md) now covers both three and four omissions with a single ordering rule (padding a triple with a temporary zero turns it into a quartet). What follows below is the original **edge-splitting** proof, which is also useful on its own because its first half is the standard opposite-pair cycle construction referenced elsewhere in this repository.

## Reduction to opposite pairs plus an optional triple

The case $p = 2$ is immediate ($\emptyset$ and $\{1\}$ both work). For an odd prime $p$, the [zero-sum reduction](README.md#reduction-to-sets-of-sum-zero) allows us to assume that $\sum A \equiv 0 \pmod p$.

Because the full set $\mathbb{F}_p^\times$ sums to $0$, the complement $C = \mathbb{F}_p^\times \setminus A$ also sums to $0 \pmod p$ and has size $|C| \le 3$. That leaves only three possibilities for $C$:
* $C = \emptyset$: $A = \mathbb{F}_p^\times$ consists purely of opposite pairs $\{d, -d\}$.
* $|C| = 2$: $C$ must be an opposite pair $\{c, -c\}$, so $A$ still consists purely of opposite pairs.
* $|C| = 3$: $C$ contains no opposite pair (otherwise its third element would be $0$). Taking negatives, the elements of $-C \subseteq A$ are three unpaired residues in $A$ summing to $0$, while all remaining elements of $A$ form opposite pairs $\{d, -d\}$.

(Note that $|C| = 1$ is impossible because a single nonzero residue cannot sum to $0$.)

### Make a cycle from opposite pairs

We first handle the case where $A$ consists entirely of opposite pairs (following [Alspach, Gavlas, Šajna and Verrall, proof of Lemma 3.4](https://core.ac.uk/download/pdf/81154598.pdf#page=6)). The empty set needs no steps, so suppose there are $n \ge 1$ pairs.

Write the positive representatives of the pairs in strictly decreasing order:
$$D = d_1 > d_2 > \cdots > d_n > 0, \qquad D \le \frac{p - 1}{2}.$$

1. **Outbound alternating walk.** Start at $x_0 = 0$ and take steps $+D, -d_2, +d_3, \ldots$ to obtain vertices $x_1, x_2, \ldots, x_n$. Because the step magnitudes strictly decrease and their signs alternate, each new vertex after $x_1$ lands strictly inside the open segment of the preceding edge ($x_1 = D$, $x_2 = D - d_2 \in (0, D)$, $x_3 = x_2 + d_3 \in (x_2, x_1)$, and so on). Therefore $x_1, \ldots, x_n$ are pairwise distinct integers in $[1, D]$.
2. **Shifted return walk.** Close the walk back to $0$ by appending the vertices
   $$x_n - D, \quad x_{n-1} - D, \quad \ldots, \quad x_1 - D = 0.$$
   Wait — what steps connect these return vertices? Moving from $x_n$ to $x_n - D$ takes the step $-D$. Moving from $x_j - D$ to $x_{j-1} - D$ takes the step $-(x_j - x_{j-1})$, the exact negative of the outbound step from $x_{j-1}$ to $x_j$. Thus the full closed walk uses every magnitude $d_1, \ldots, d_n$ exactly once in each direction!

Because $x_1, \ldots, x_n \in [1, D]$ are distinct, their translates $x_n - D, \ldots, x_1 - D$ are distinct integers in $[1 - D, 0]$. The entire range $[1 - D, D]$ contains $2D \le p - 1 < p$ consecutive integers, so no two vertices collide modulo $p$ and the cycle stays simple.

### Split one edge to insert the triple

Now suppose $A$ consists of opposite pairs together with three unpaired residues summing to $0 \pmod p$.

**Step 1: Normalize the triple to $\{1, r, -(r+1)\}$.** Scale the entire set $A$ so that one unpaired element becomes $1$. The other two unpaired elements sum to $-1 \equiv p - 1 \pmod p$, so their least positive representatives in $\{1, \ldots, p-1\}$ sum to $p - 1$ (and are distinct, since $p - 1$ is even and equality would make the two elements identical). Let $r$ be the smaller of those two representatives; then $2 \le r < (p - 1)/2$ and the third element is $-(r + 1) \pmod p$. Put $L = r + 1$, so the unpaired triple is $\{1, r, -L\}$.

**Step 2: Build a proxy cycle.** Temporarily replace the triple $\{1, r, -L\}$ by the opposite pair $\{L, -L\}$ and form the opposite-pair cycle from the previous section. Because $r$ and $-L$ were unpaired in $A$, neither magnitude $r$ nor magnitude $L$ appeared among $A$’s original opposite pairs; in particular, **the proxy cycle has no pair of magnitude $r = L - 1$**.

**Step 3: Spot an unoccupied point on the edge of length $L$.** Look at the edge $u \to v$ of length $L$ on the outbound alternating part of the walk. Let $w$ be the integer point one unit from $u$ toward $v$ (so $w$ splits the step of length $L$ into steps of lengths $1$ and $L - 1 = r$). **We claim $w$ is not visited anywhere else in the cycle:**

* *Earlier outbound vertices:* by nesting of the alternating walk, every earlier vertex lies outside the open edge between $u$ and $v$.
* *Later outbound vertices:* the very next step after $v$ (if any) has magnitude strictly less than $L$, and it cannot be $r = L - 1$ because magnitude $r$ is absent from the proxy cycle. Hence the next step has magnitude at most $L - 2$. By nesting, every subsequent outbound vertex remains within distance $L - 2$ of $v$ — whereas $w$ sits at distance $L - 1$ from $v$.
* *Return vertices:* every return vertex lies in $[1 - D, 0] \le 0$, whereas $u \ge 0$ and $v \ge 1$ force the interior point $w$ to be strictly positive.

**Step 4: Insert $w$ and orient the cycle.** Insert $w$ between $u$ and $v$ to obtain a simple cycle with one extra vertex. Traverse this cycle in whichever direction makes the split edge run positively (if the outbound edge was $+L$, keep the direction; if it was $-L$, reverse the entire cycle, which negates every step and keeps all partial sums distinct). The split edge now contributes the steps $1$ and $r$ in some order, while the unsplit copy of the edge on the other half of the cycle contributes $-L$, and every opposite pair still contributes $\pm d$. Undoing the initial scaling yields the required Graham ordering of $A$.

Notice that this argument works verbatim for *any* collection of opposite pairs together with three unpaired elements summing to zero. $\square$

## Worked example (modulo 11)

Consider $A = \{1, 2, 4, 5, 6, 7, 8\} \subseteq \mathbb{F}_{11}^\times$. Pairing opposite residues gives $\pm 4$ ($\{4, 7\}$) and $\pm 5$ ($\{5, 6\}$), leaving the unpaired zero-sum triple $\{1, 2, 8\} = \{1, 2, -3\}$ (so $r = 2$ and $L = 3$).

1. Temporarily replace $\{1, 2, -3\}$ by $\pm 3$. The opposite-pair cycle for $\pm 5, \pm 4, \pm 3$ visits the vertices
   $$0 \xrightarrow{+5} 5 \xrightarrow{-4} 1 \xrightarrow{+3} 4 \xrightarrow{-5} -1 \xrightarrow{-3} -4 \xrightarrow{+4} 0.$$
2. On the outbound walk, the edge of length $L = 3$ is $1 \to 4$. Inserting $w = 2$ (one unit from $1$ toward $4$) splits the step $+3$ into $+1, +2$.
3. The resulting simple cycle is $0, 5, 1, 2, 4, -1, -4, 0$ (steps $5, -4, 1, 2, -5, -3, 4$, i.e., $5, 7, 1, 2, 6, 8, 4 \pmod{11}$). Its seven nonempty partial sums are $5, 1, 2, 4, -1, -4, 0$ — all distinct modulo $11$.

## Executable constructor and tests

The Python [witness constructor](paired_triple.py) implements the newer unified ordering rule and verifies every ordering it produces:

~~~sh
python3 paired_triple.py --example 11 1 2 4 5 6 7 8
python3 paired_triple.py --through 257
~~~
