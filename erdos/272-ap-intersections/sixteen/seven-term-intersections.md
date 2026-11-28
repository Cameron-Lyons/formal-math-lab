# Bounds for families with short intersections

What is the maximum size of an AP-intersecting family on $[N] = \{1, \ldots, N\}$ if we cap the *length* of every pairwise intersection at $L$ terms (while letting the sets themselves be arbitrarily large)? Write $t_L(N)$ for this maximum, and set
$$
H = 1 + \binom{N}{2}, \qquad k = \left\lfloor \frac{N - 1}{4} \right\rfloor .
$$
For every $N \ge 1$, the first five values are known exactly:

| Maximum intersection length $L$ | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: |
| $t_L(N)$ | $N$ | $H$ | $H$ | $H + k$ | $H + k$ |

Beyond $L = 5$, we establish sharp linear-algebraic bounds for intersections of at most six or seven terms—both in terms of the number of distinct long intersections realized and in terms of the rank of the seven-term progression incidence matrix.

## Exact values for $L = 1, 2, 3$

### Singletons only ($L = 1$): $t_1(N) = N$

- **Lower bound:** Take the singleton $\{x\}$ together with all $N - 1$ pairs containing $x$. Every two distinct sets meet in $\{x\}$.
- **Upper bound (Fisher-style Gram matrix):** Assume $|F| \ge 2$ and assign each $A \in F$ its point-incidence vector in $\mathbb{R}^N$. Their Gram matrix $G_{AB} = |A \cap B|$ has off-diagonal entries $1$ and diagonal entries $|A|$, so its quadratic form is
  $$
  c^{\mathsf T} G c = \Bigl(\sum_{A \in F} c_A\Bigr)^2 + \sum_{A \in F} (|A| - 1) c_A^2.
  $$
  Every member is nonempty ($|A| \ge 1$), and at most one member is a singleton (two distinct singletons would be disjoint). If $c^{\mathsf T} G c = 0$, every term $(|A| - 1)c_A^2$ vanishes, killing $c_A$ for all $|A| \ge 2$; then $(\sum c_A)^2 = 0$ kills the possible singleton as well. Thus the incidence vectors are linearly independent in $\mathbb{R}^N$, giving $|F| \le N$.

### Pairs and triples ($L = 2, 3$): $t_2(N) = t_3(N) = H$

- **Lower bound:** All $1 + (N - 1) + \binom{N - 1}{2} = 1 + \binom{N}{2} = H$ sets of size at most three containing a fixed point $x$ meet pairwise in one or two elements.
- **Upper bound for $L = 3$:** Let $a_3(S)$ count the three-term progressions contained in $S$, and define the score
  $$
  q_3(S) = \binom{|S| - 1}{2} - a_3(S) = 1 + \binom{|S|}{2} - |S| - a_3(S).
  $$
  *Why is $q_3(S) \ge 0$, vanishing precisely on progressions of at most three terms?* For $|S| = m \le 3$, direct check gives $0$ on singletons, pairs, and 3-term progressions, and $1$ on a nonprogression triple. For $m \ge 4$, list the elements of $S$ in increasing order: the point with $i$ predecessors and $m - 1 - i$ successors can be the middle element of at most $\min(i, m - 1 - i)$ three-term progressions in $S$. Summing over $i = 0, \ldots, m - 1$ gives
  $$
  a_3(S) \le \sum_{i = 0}^{m - 1} \min(i, m - 1 - i) = \left\lfloor \frac{(m - 1)^2}{4} \right\rfloor < \binom{m - 1}{2}
  $$
  for all $m \ge 4$ (as $\binom{m - 1}{2} - \frac{(m - 1)^2}{4} = \frac{(m - 1)(m - 3)}{4} > 0$).

  Now give each $A \in F$ a positive vector $u_A \in \mathbb{R}^H$ (constant $1$ and all pair indicators) and a negative vector $v_A$ (singleton and three-term progression indicators). Then $u_A \cdot u_B - v_A \cdot v_B = q_3(A \cap B)$, which vanishes for distinct $A, B \in F$. Squaring any linear relation $\sum c_A u_A = 0$ (just as in the five-term proof below) shows $0 = \|\sum c_A v_A\|^2 + \sum c_A^2 q_3(A)$, forcing $c$ to be supported on progressions of lengths 1 through 3 and to annihilate both $u$ and $v$. Since every progression of length 1, 2, or 3 indexes its own containment coordinate, an inclusion-maximal set with nonzero coefficient would give a nonzero value at its own coordinate—impossible. Hence the $u_A$ are linearly independent in $\mathbb{R}^H$, proving $|F| \le H$ (even for families with a common point!). Families of size $\le 1$ satisfy the bound directly.

## Exact maximum when intersections have at most five terms

**Theorem.** For every $N \ge 1$, among families on $[N]$ whose pairwise intersections are nonempty progressions of at most five terms (with no bound on member sizes), the exact maximum is
$$
1 + \binom{N}{2} + \left\lfloor \frac{N - 1}{4} \right\rfloor = H + k.
$$
The same maximum holds with four in place of five.

Szabó's construction attains $H + k$ using distinct sets of size at most five (so no two can share five points). Yang's starred-family theorem supplies the matching upper bound $H + k$ whenever the entire family shares a common point. [Szabó, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) · [Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004)

For the remaining case (empty total intersection), we prove a stronger statement:

**Proposition.** Let $F$ be an admissible family on $[N]$ with $\bigcap_{A \in F} A = \varnothing$, and let $G \subseteq F$ be any subfamily whose pairwise intersections all have length at most five. Then $|G| \le H = 1 + \binom{N}{2}$ (even if $G$ itself has a common point).

**Proof.** Families with $|G| \le 1$ satisfy $|G| \le H$ trivially. For a nonempty integer set $S$ of size $m$, let $a_j(S)$ count its $j$-term progressions and define
$$
q_5(S) = \binom{m - 1}{2} - a_3(S) - a_4(S) = Q(S) + \bigl(a_6(S) - a_7(S)\bigr),
$$
where $Q(S) = \binom{m - 1}{2} - a_3(S) - a_4(S) - a_6(S) + a_7(S)$ is the general score from the fourteen-point proof, which satisfies $Q(S) \ge 0$ with $Q(S) = 0$ forcing $S$ to be an arithmetic progression ([general score inequality and equality proof](https://github.com/Cameron-Lyons/formal-math-lab/blob/cb3ea3b96b699e62d1a29f2e4e3e0b11cadafccb/erdos-272-fourteen/score.md)).

Observe what $a_6(S) - a_7(S)$ counts: along any fixed step $d$, a maximal run of length $r \ge 6$ contains $r - 5$ six-term progressions and $r - 6$ seven-term progressions, contributing $(r - 5) - (r - 6) = 1$ (while runs of length $< 6$ contribute $0$). Thus $a_6(S) - a_7(S)$ equals the total number of maximal runs of length at least six, summed over all steps. In particular:

- If $S$ is a progression of length $\ge 6$, the run along its own step contributes at least $1$, so $q_5(S) \ge 1 > 0$.
- If $S$ is a progression of length $m \in \{1, 2, 3, 4, 5\}$, direct count gives $a_3(S) + a_4(S) = 0, 0, 1, 3, 6$, matching $\binom{m - 1}{2} = 0, 0, 1, 3, 6$, so $q_5(S) = 0$.

Hence $q_5(S) \ge 0$ on all nonempty sets, vanishing precisely on progressions of at most five terms.

Now give each $A \in G$ a positive vector $u_A \in \mathbb{R}^H$ (constant $1$ and all pair indicators) and a negative vector $v_A$ (singleton, three-term, and four-term progression indicators). Counting common coordinates gives $u_A \cdot u_B - v_A \cdot v_B = q_5(A \cap B)$, which is $0$ for distinct $A, B \in G$. Any real relation $\sum_{A \in G} c_A u_A = 0$ therefore yields
$$
0 = \left\|\sum_{A \in G} c_A v_A\right\|^2 + \sum_{A \in G} c_A^2 q_5(A).
$$
Thus $c$ vanishes outside progressions of lengths at most five and annihilates both $u$ and $v$. Every progression of length $1, 2, 3,$ or $4$ indexes its own containment coordinate in $(u, v)$; only length $5$ does not. Applying the [five-term relation argument](signed-rank.md#the-five-term-relations), any nonzero relation would force two pairs $\{a, x\}$ and $\{x, b\}$, their five-term progression $P$, and its middle triple $M$ into $G \subseteq F$. Since $\bigcap_{A \in F} A = \varnothing$, some member $B \in F$ omits $x$. To meet both pairs $\{a, x\}$ and $\{x, b\}$, $B$ must contain both $a$ and $b$. The only progression in $P$ containing $a$ and $b$ while omitting $x$ is $\{a, b\}$, leaving $B \cap M = \varnothing$—contradicting admissibility of $F$. Thus the $u_A$ ($A \in G$) are linearly independent in dimension $H$, proving $|G| \le H$. $\square$

**Matching corollary for unrestricted families.** Given any unrestricted admissible family $F$ with empty total intersection, form the graph whose edges connect pairs of members intersecting in at least six terms. Deleting any vertex cover $U$ leaves a subfamily $G$ whose pairwise intersections all have at most five terms, so $|F| - |U| \le H$, i.e., $|U| \ge |F| - H$. Because the $2|M|$ endpoints of a maximal matching $M$ form a vertex cover, $F$ contains at least $\lceil (|F| - H)/2 \rceil$ disjoint pairs of members with intersections of at least six terms. On sixteen points ($H = 121$), any 125-member family must contain at least **two disjoint pairs** of members whose intersections have at least six terms.

### Allowing one six-term progression as an intersection

Suppose every pairwise intersection has at most six terms and at most **one** distinct six-term progression $P$ occurs as an intersection (though arbitrarily many pairs of sets may intersect in $P$). Then the exact maximum is again Szabó's formula $H + k$ for every $N$.

**Proof.** When $P$ occurs and $\bigcap F = \varnothing$, add the containment indicator $1_{P \subseteq A}$ to the negative vector $v_A$ from the five-term proof. The new score is $q_5(A) - 1_{P \subseteq A}$:

- **Off the diagonal:** Every intersection of length $\le 5$ has score $0$, and at $P$ itself $q_5(P) - 1 = 1 - 1 = 0$.
- **On the diagonal:** Whenever $P \subseteq A$, the maximal run in $A$ extending $P$ contributes at least $1$ to $a_6(A) - a_7(A)$, so $q_5(A) - 1_{P \subseteq A} \ge Q(A) \ge 0$. Equality forces $Q(A) = 0$, which (as proved in [The score](#the-score) below) means $A$ is a progression of length at most seven.

Besides progressions of length $\le 5$, the only possible zero-score rows are $P$ itself and the at most **two** seven-term progressions extending $P$ by one point at either end (any six-term progression inside a seven-term progression must share its step and consist of six consecutive terms). Give each of those at most two seven-term extensions its own positive equality coordinate $1_{A = R}$. In any linear relation on the positive vectors, the equality coordinates kill the seven-term coefficients, and $P$ now has its own negative containment coordinate. Subtracting the five-term relations leaves no nonzero relation by the same forced-pair argument, proving $|F| \le H + 2$.

For $N \ge 9$, $2 \le \lfloor (N - 1)/4 \rfloor = k$, so $H + 2 \le H + k$. For $N \le 8$, the unconditional exact values give the result directly (with $N = 1, 2$ immediate). [Yang, Theorem 1.1](https://arxiv.org/abs/2607.23004)

### Several distinct six- or seven-term intersections

The single-progression trick generalizes cleanly when multiple six- or seven-term progressions appear as intersections.

**Corollary.** Suppose $F$ has empty total intersection, all pairwise intersections have at most seven terms, and $t$ distinct six- or seven-term progressions actually occur as pairwise intersections. Then
$$
|F| \le H + 2t.
$$
In particular, Szabó's upper bound $|F| \le H + k$ holds whenever $2t \le \lfloor (N - 1)/4 \rfloor$ (including the case of intersections of length $\le 6$, where $t$ counts distinct six-term intersections).

This corollary is a special case of a finer structural theorem built by grouping six-term "windows" into consecutive blocks along each arithmetic line.

**Theorem.** Suppose $F$ has empty total intersection and all pairwise intersections have at most seven terms. Let $W$ be a nonempty collection of six-term progressions containing every realized six-term intersection and at least one of the two six-term windows of every realized seven-term intersection. Set $s = |W|$.

Group the windows in $W$ by their arithmetic line—that is, by their step $d$ and the residue of their first element modulo $d$. Let $g$ be the number of nonempty lines. Along each line $i$, order the starting points of windows in $W$, and partition them into **blocks**: maximal sequences of consecutive starting points spaced exactly $d$ apart. Let $c_i$ be the number of blocks on line $i$, and put $c = \sum_i c_i$. Then
$$
|F| \le H + s - g + \sum_i \min(2c_i, 5) \le H + s - g + 2c.
$$
Moreover, if $W$ specifically contains the **left** six-term window of every realized seven-term intersection, then the sharper bound
$$
|F| \le H + s + c
$$
also holds.

*Deducing the corollary:* If neither six- nor seven-term intersections occur, the five-term theorem gives $|F| \le H$. Otherwise, let $W$ consist of all realized six-term intersections together with the left six-term window of every realized seven-term intersection. Then $c \le s \le t$, so $|F| \le H + s + c \le H + 2t$.

**Proof of the theorem.** To visualize the setup, picture a single arithmetic line of step $d$ where $W$ has windows starting at $1, 2, 3$ (block 1) and $6, 7$ (block 2). Inside each block, adjacent windows overlap in five terms and glue together into a seven-term progression; between blocks, any set bridging the gap must contain a long run of at least eight terms.

1. **Deleting at most $c - g$ bridging members:** For each member $A \in F$ and each step $d$, decompose $A$ into maximal runs of consecutive points with step $d$. Every window of $W$ with step $d$ contained in $A$ lies inside a unique maximal run. Delete any member $A \in F$ that contains two windows from *different* blocks within the same maximal run.
   - Because the windows inside one maximal run form an interval along that line, a deleted member contains the entire progression from the last window of some block to the first window of the next block on that line.
   - Since those two blocks are separated by a gap of at least $2d$ between their starting points, that spanning progression has at least $6 + 2 = 8$ terms. No two distinct members of $F$ can both contain it (their intersection would have $\ge 8$ terms).
   - Across all $g$ lines there are $\sum_i (c_i - 1) = c - g$ consecutive pairs of blocks, so **at most $c - g$ members are deleted**.

2. **Building the modified score $q_*$:** Within each block, every pair of windows with consecutive starts ($y$ and $y + d$) has union equal to a seven-term progression. Let $K$ be the set of all these seven-term unions; since a block of $r$ windows produces $r - 1$ unions, $|K| = s - c$, and each $R \in K$ is uniquely determined by its two windows in $W$. Starting from the $(u, v)$ coordinates for $q_5$, add a **negative** containment coordinate for each $P \in W$ and a **positive** containment coordinate for each $R \in K$. The resulting score is
   $$
   q_*(S) = q_5(S) - \#\{P \in W : P \subseteq S\} + \#\{R \in K : R \subseteq S\}.
   $$
   - *Off-diagonal vanishing:* On intersections of length $\le 5$, $q_*(S) = q_5(S) = 0$. On a realized six-term intersection $P \in W$, $q_*(P) = 1 - 1 + 0 = 0$. On a realized seven-term intersection $R$, $q_5(R) = 1$, and $R$'s only six-term subprogressions are its two consecutive windows: if $W$ contains one window, $R \notin K$ and $q_*(R) = 1 - 1 + 0 = 0$; if $W$ contains both windows, their starts are consecutive so $R \in K$ and $q_*(R) = 1 - 2 + 1 = 0$.
   - *Nonnegative diagonals on surviving members:* For any surviving member $A$, the windows of $W$ contained in a given maximal run are either absent or all come from a single block. If a run contains $h > 0$ windows, their starts are consecutive, so the run also contains exactly $h - 1$ progressions from $K$, contributing $h - (h - 1) = 1$ (and $0$ if $h = 0$). Summing over all steps and maximal runs gives
     $$
     \#\{P \in W : P \subseteq A\} - \#\{R \in K : R \subseteq A\} \le a_6(A) - a_7(A),
     $$
     since the right side counts *all* maximal runs of length $\ge 6$. Hence $q_*(A) \ge Q(A) \ge 0$, with $q_*(A) = 0$ forcing $Q(A) = 0$ and thus (by [The score](#the-score) below) forcing $A$ to be a progression of length at most seven.

3. **Accounting for zero-score progressions:** What zero-score progressions can survive without their own containment coordinate?
   - Length $\le 5$: handled as in the five-term proof.
   - Length $6$: to have $q_*(A) = 0$, $A$ must belong to $W$ and therefore indexes a negative containment coordinate.
   - Length $7$: to have $q_*(A) = 0$, $A$ must contain at least one window of $W$. If it contains *both* of its six-term windows in $W$, then $A \in K$ already indexes a positive containment coordinate. If it contains *only one* window of $W$, it must extend the first window of some block one step to the left or the last window of some block one step to the right—at most $2c_i$ candidates on line $i$.
   - *Why at most $\min(2c_i, 5)$ singly covered seven-term members can coexist on line $i$:* Any two seven-term progressions on line $i$ in $F$ must intersect, so all their starting points lie inside seven consecutive grid positions of step $d$ (if two starts were $7d$ apart, the progressions would be disjoint). Moreover, *three consecutive starts* $y, y + d, y + 2d$ cannot all occur: the intersection of the first two is the left six-term window of the middle progression, and the intersection of the last two is its right six-term window, which would force *both* windows of the middle progression into $W$ (contradicting single coverage). From 7 consecutive positions, at most **5** can be chosen without 3 consecutive (split into $\{1,2,3\}, \{4,5,6\}, \{7\}$: at most $2 + 2 + 1 = 5$).

4. **Linear independence:** Add one positive equality coordinate $1_{A = R}$ for each singly covered seven-term member actually present among the surviving sets. These preserve $q_*(A \cap B) = 0$ off the diagonal and only increase diagonals. In any relation on the positive rows, squaring kills all non-zero-score rows and annihilates the negative coordinates; the equality coordinates kill all singly covered seven-term rows; every remaining possible support progression except length 5 indexes its own containment coordinate. Subtracting the five-term relations and invoking an omitting member from the original family $F$ kills the relation completely. Thus the surviving rows are independent in at most $H + (s - c) + \sum_i \min(2c_i, 5)$ positive coordinates. Restoring the at most $c - g$ deleted bridging members gives
   $$
   |F| \le H + (s - c) + (c - g) + \sum_i \min(2c_i, 5) = H + s - g + \sum_i \min(2c_i, 5) \le H + s - g + 2c.
   $$

5. **The sharper bound $|F| \le H + s + c$:** Suppose $W$ contains the *left* six-term window of every realized seven-term intersection, and let $m \le c - g$ be the actual number of deleted bridging members (each charged to a distinct gap between consecutive blocks). For a charged gap on a line of step $d$, let $j$ be the first start of the block on the right of the gap, and let $R$ be the seven-term progression starting at $j - d$ (the leftward outward extension of that block). The bridging member $B$ charged to this gap contains $R$ and has $|B| \ge 8$. If $R$ were also a member of $F$, then $B \cap R = R$ would be a realized seven-term intersection, so its left six-term window (starting at $j - d$) would have to lie in $W$—contradicting the gap immediately before $j$! Thus each of the $m$ bridging members rules out a distinct outward extension among the $2c$ possible ones, leaving at most $2c - m$ equality coordinates and giving
   $$
   |F| \le H + (s - c) + (2c - m) + m = H + s + c. \quad \square
   $$

## Intersections of at most seven terms

When pairwise intersections have at most seven terms, we also obtain a clean rank bound directly from the seven-term progressions contained in $F$.

**Theorem.** Let $F$ be an admissible family on $[N]$ with empty total intersection and at least two members, such that every two distinct members intersect in an arithmetic progression of at most seven terms (individual members may be arbitrarily large). Let $M$ be the $0\text{--}1$ incidence matrix with one row per member $A \in F$ and one column per seven-term progression $P$ contained in at least one member of $F$, where $M_{A,P} = 1$ if $P \subseteq A$ and $0$ otherwise. Then
$$
|F| \le 1 + \binom{N}{2} + \operatorname{rank}_{\mathbb{R}} M.
$$

In particular, if at most $k = \lfloor (N - 1)/4 \rfloor$ distinct seven-term progressions appear inside members of $F$, then $|F| \le 1 + \binom{N}{2} + k$. Together with Yang's bound for families with a common point and Szabó's attaining construction (which uses sets of size at most five), this bound is sharp for every $N$ under these two restrictions. [Yang, Theorems 1.2 and 1.4](https://arxiv.org/abs/2607.23004)

## The score

For any nonempty finite integer set $S$, define
$$
Q(S) = \binom{|S| - 1}{2} - a_3(S) - a_4(S) - a_6(S) + a_7(S).
$$
The general score inequality from the fourteen-point proof establishes $Q(S) \ge 0$ for all nonempty $S$, and proves that $Q(S) = 0$ forces $S$ to be an arithmetic progression ([general score inequality and equality argument](https://github.com/Cameron-Lyons/formal-math-lab/blob/cb3ea3b96b699e62d1a29f2e4e3e0b11cadafccb/erdos-272-fourteen/score.md)).

**Exact characterization of zeros:** $Q(S) = 0$ if and only if $S$ is an arithmetic progression of length at most seven.

- *Lengths 1 through 6:* Already checked in the earlier score calculation (for lengths 1–5, $a_6 = a_7 = 0$ and $q_5 = 0$; at length 6, $q_5 = 1$, $a_6 = 1$, $a_7 = 0$, giving $Q = 0$).
- *Length 7:* On $[7]$, the counts are $a_3 = 9$, $a_4 = 5$, $a_6 = 2$, $a_7 = 1$, and $\binom{6}{2} = 15$, giving $Q([7]) = 15 - 9 - 5 - 2 + 1 = 0$.
- *Lengths $m \ge 8$:* Since progression counts are affine-invariant, it suffices to check $S = [m]$ with $m \ge 8$. In the notation of the score proof, let $H_d$ and $L_d$ count the maximal runs of step $d$ in $[m]$ of lengths at least $3$ and at least $6$, respectively; set $D = \{d : H_d > 0\}$ and $R = \sum_d (H_d - L_d)$. On an interval $[m]$, all centre deficits vanish, so $Q([m]) = R - |D|$. Reindexing $\sum_d L_d = \sum_{d\text{ even}} L_{d/2}$ decomposes $R$ as
  $$
  R = \sum_{d\text{ odd}} H_d + \sum_{d\text{ even}} (H_d - L_{d/2}).
  $$
  By the run-count inequality in the score proof, each summand is at least $1$ for every $d \in D$ and nonnegative otherwise. When $m \ge 8$, the odd step $d = 3$ has at least **two** distinct maximal runs of length $\ge 3$—one containing $\{1, 4, 7\}$ and another containing $\{2, 5, 8\}$—so $H_3 \ge 2$. Therefore $R \ge |D| + 1$, giving $Q([m]) > 0$.

## Independence

For each $A \in F$, form the positive vector $u_A$ from the constant $1$, all $\binom{N}{2}$ pair-containment indicators, and the row of $M$ corresponding to $A$. Form the negative vector $v_A$ from the containment indicators of singletons and progressions of lengths $3$, $4$, and $6$. Counting common coordinates yields
$$
u_A \cdot u_B - v_A \cdot v_B = Q(A \cap B).
$$
For distinct $A, B \in F$, $A \cap B$ is a progression of length at most seven, so $Q(A \cap B) = 0$. Just as in the sixteen-point signed-rank argument, any linear relation $\sum_{A \in F} c_A u_A = 0$ implies
$$
0 = \left\|\sum_{A \in F} c_A v_A\right\|^2 + \sum_{A \in F} c_A^2 Q(A).
$$
Consequently, $c$ annihilates both $u$ and $v$ and is supported exclusively on progression members of length at most seven. Among lengths 1 through 7, only length 5 lacks its own containment coordinate in $(u, v)$. Subtracting the five-term inclusion–exclusion relation $c_P w_{x,d}$ for each five-term progression $P$ and checking an inclusion-maximal remaining support member at its own coordinate proves that $c$ lies in the span of the five-term relations. The forced-pair, five-term progression, and middle-triple contradiction from the [signed-rank proof](signed-rank.md#the-five-term-relations) applies verbatim for every $N$, showing $c = 0$.

Therefore the vectors $u_A$ ($A \in F$) are linearly independent. Since they lie in the column space spanned by the constant, the $\binom{N}{2}$ pair columns, and the columns of $M$, we conclude $|F| \le 1 + \binom{N}{2} + \operatorname{rank}_{\mathbb{R}} M$. $\square$
