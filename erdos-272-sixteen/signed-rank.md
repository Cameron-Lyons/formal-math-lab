# A rank bound for families on sixteen points

How do we obtain an unconditional upper bound on $t(16)$—covering families with *empty total intersection* and *unrestricted intersection lengths*? The centerpiece is a **Möbius-weighted signed-rank theorem** that maps every family member to a linearly independent real vector, followed by a finite case split over which of the fourteen seven-term progressions appear in the family. Together, they establish **$124 \le t(16) \le 132$**.

## The main linear-independence theorem

Let $F$ be a family of at least two distinct subsets of $[16]$ with empty total intersection ($\bigcap_{A \in F} A = \varnothing$), such that every two distinct members intersect in a nonempty arithmetic progression. For each member $A \in F$, form a real row vector consisting of:

- the constant $1$;
- the containment indicators $1_{P \subseteq A}$ for all arithmetic progressions $P \subseteq [16]$ of lengths **$2, 7, 11, 15,$ and $16$**;
- the equality indicators $1_{A = P}$ for all arithmetic progressions $P \subseteq [16]$ of lengths **$9, 10,$ and $13$**.

**Theorem.** These row vectors are linearly independent over $\mathbb{R}$.

Counting all available columns on $[16]$ gives an immediate unconditional ceiling before any coordinates are pruned:
$$
\underbrace{1}_{\text{const}} + \underbrace{120}_{\text{len }2} + \underbrace{14}_{\text{len }7} + \underbrace{6}_{\text{len }11} + \underbrace{2}_{\text{len }15} + \underbrace{1}_{\text{len }16} + \underbrace{8}_{\text{len }9} + \underbrace{7}_{\text{len }10} + \underbrace{4}_{\text{len }13} = 163.
$$
Better still, any column that is identically zero on $F$ can be dropped: for a prescribed family $F$, the theorem bounds $|F|$ by **$121$ plus the number of progressions of lengths $7, 11, 15, 16$ contained in at least one member of $F$, plus the number of members of $F$ equal to a progression of length $9, 10,$ or $13$**.

## Signed count

**The big idea (linear algebra with signed inner products).** Classical linear-algebra bounds in extremal combinatorics (like Fisher's inequality or the Babai–Frankl method) embed sets as vectors $u_A$ whose Gram matrix $u_A \cdot u_B$ is diagonal with positive diagonal entries. Here, pairwise intersections $A \cap B$ can be *any* of the 330 nonempty arithmetic progressions in $[16]$, so a single positive dot product cannot vanish on all of them at once.

Instead, we split coordinates into **positive** coordinates $u_A$ and **negative** coordinates $v_A$, engineering a *signed* inner product $u_A \cdot u_B - v_A \cdot v_B = q(A \cap B)$ that equals $0$ on every nonempty progression and is strictly positive on every nonprogression. Then any linear dependence $\sum c_A u_A = 0$ on the positive vectors alone forces $0 = \|\sum c_A v_A\|^2 + \sum c_A^2 q(A)$, simultaneously killing every nonprogression coefficient and forcing the relation to annihilate the negative coordinates as well!

**Choosing the weights via the Möbius function.** Assign the empty set $\varnothing$ weight $1$, and assign every nonempty arithmetic progression of length $k$ a weight depending only on $k$:

| Length $k$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Weight | $-1$ | $1$ | $-1$ | $-1$ | $0$ | $-1$ | $1$ | $-1$ | $0$ | $0$ | $1$ | $-1$ | $0$ | $-1$ | $1$ | $1$ |

For every $k \ge 2$, the weight is the classical number-theoretic **Möbius function** $\mu(k - 1)$ (which equals $+1$ if $k - 1$ is a product of an even number of distinct primes, $-1$ if an odd number, and $0$ if $k - 1$ is divisible by a square). Notice how the positive weights $+1$ land precisely on lengths $2, 7, 11, 15, 16$, while lengths $5, 9, 10, 13$ have weight $0$.

For any subset $S \subseteq [16]$, define its score $q(S)$ as the sum of weights of $\varnothing$ and all nonempty arithmetic progressions contained in $S$.

**Why $q(P) = 0$ on every nonempty progression $P$:** Let $P$ have length $L$ and step $d$. Group all subprogressions of $P$ of length $\ge 2$ by their pair of endpoints $x < y$. If $x$ and $y$ are $s$ steps apart in $P$ ($y - x = s d$), then a subprogression of $P$ with endpoints $x$ and $y$ splits the $s$ steps into $r$ equal sub-steps for some divisor $r \mid s$, giving length $k = r + 1$ and weight $\mu(r)$. Summing over all subprogressions with endpoints $x, y$ yields
$$
\sum_{r \mid s} \mu(r) = \begin{cases} 1 & \text{if } s = 1 \text{ (consecutive points of } P\text{)}, \\ 0 & \text{if } s \ge 2. \end{cases}
$$
Thus only the $L - 1$ consecutive pairs of $P$ survive, contributing $L - 1$ in total, which cancels the constant $+1$ and the $L$ singleton weights $(-1)$: $q(P) = 1 - L + (L - 1) = 0$.

**Positivity on nonprogressions:** On $[16]$, there are $330$ nonempty arithmetic progressions (all having $q(S) = 0$) and $2^{16} - 1 - 330 = 65{,}205$ nonempty nonprogressions. The [Python verifier](signed_rank.py) computes $q(S)$ on every subset and verifies that **$q(S) > 0$ on all 65,205 nonprogressions**. (Run `python3 signed_rank.py` from this directory.)

**Squaring a relation:** Let $u_A$ record the constant $1$ and containment in $A$ of all positively weighted progressions (lengths $2, 7, 11, 15, 16$), and let $v_A$ record containment in $A$ of all negatively weighted progressions (lengths $1, 3, 4, 6, 8, 12, 14$). Counting common coordinates gives
$$
u_A \cdot u_B - v_A \cdot v_B = q(A \cap B).
$$
Suppose a real linear relation with coefficients $c_A$ ($A \in F$) holds among the rows of the theorem. The equality coordinates $1_{A = P}$ immediately force $c_P = 0$ for every progression member of length $9, 10,$ or $13$. Moreover, $\sum_{A \in F} c_A u_A = 0$. Taking the squared norm and using $q(A \cap B) = 0$ for distinct $A, B \in F$ gives
$$
0 = \left\|\sum_{A \in F} c_A u_A\right\|^2 = \left\|\sum_{A \in F} c_A v_A\right\|^2 + \sum_{A \in F} c_A^2 q(A).
$$
Because every term is nonnegative and $q(A) > 0$ on nonprogressions, all nonprogression coefficients vanish ($c_A = 0$) and $\sum_{A \in F} c_A v_A = 0$ as well. Extend $c$ by zero to all progressions outside $F$.

## The five-term relations

Every remaining progression with a potentially nonzero coefficient $c_P$ has length other than $9, 10, 13$. Every such length **except length 5** has a nonzero Möbius weight and therefore indexes its own containment coordinate in $(u, v)$. Just as in [rank-mark.md](rank-mark.md#relations-among-short-progressions), the missing five-term coordinates generate one explicit inclusion–exclusion relation per five-term progression.

For a five-term progression $P = \{a, x - d, x, x + d, b\}$ of step $d$ and centre $x$, set $a = x - 2d$, $b = x + 2d$, and let $O = \{a, x, b\}$ be its outer triple. In coefficient space (with unit basis vectors $e_D$), define for any $D \supseteq \{a, b\}$:
$$
h(D) = e_D - e_{D \setminus \{a\}} - e_{D \setminus \{b\}} + e_{D \setminus \{a,b\}},
\qquad
w_{x,d} = h(P) - h(O).
$$

- **Evaluating $w_{x,d}$ on containment coordinates:** Evaluating $h(D)$ on the containment coordinate indexed by a set $T$ (summing over all $S$ with $T \subseteq S \subseteq D$) yields $1$ if $\{a, b\} \subseteq T \subseteq D$ and $0$ otherwise (if $T$ misses $a$ or $b$, terms cancel in pairs; in particular $T = \varnothing$ gives $0$). The only arithmetic progressions $T \subseteq P$ containing both endpoints $a$ and $b$ have step dividing $b - a = 4d$, namely $\{a, b\}$, $O$, and $P$. Both $h(P)$ and $h(O)$ evaluate to $1$ on $\{a, b\}$ and $O$, so $w_{x,d} = h(P) - h(O)$ evaluates to $0$ on every containment coordinate except $T = P$. Since length 5 has weight $0$ (no five-term coordinate in $(u, v)$), each $w_{x,d}$ annihilates all positive and negative containment coordinates.
- **Spanning all remaining relations:** The sole five-term progression in $w_{x,d}$ is $P$, with coefficient $+1$. Subtract $c_P w_{x,d}$ from $c$ for each five-term progression $P$. Every progression still eligible to have a nonzero coefficient indexes its own containment coordinate in $(u, v)$; taking an inclusion-maximal one would produce a nonzero value at its own coordinate. Hence the remainder is zero, and
  $$
  c = \sum_{x,d} \alpha_{x,d} w_{x,d}, \qquad \alpha_{x,d} = c_P.
  $$
- **Forcing a common centre $x$:** Set $\alpha_{x,d} = 0$ when the five-term progression at $(x, d)$ does not fit in $[16]$, and call $x$ *active* at step $d$ if $\alpha_{x,d} \ne 0$. In $w_{x,d}$, the only pairs are $\{x - 2d, x\}$ and $\{x, x + 2d\}$, both with span $2d$ and coefficient $+1$. Hence for a fixed step $d$, the total coefficient of the pair $\{u, u + 2d\}$ is $\alpha_{u,d} + \alpha_{u + 2d, d}$, with no contribution from any other step.
  - In any active residue class modulo $2d$, let $p$ be the smallest active centre and $q$ the largest. Then $\{p - 2d, p\}$ and $\{q, q + 2d\}$ have nonzero coefficients $\alpha_{p,d}$ and $\alpha_{q,d}$, forcing both pairs into $F$. If $p < q$, these two pairs are disjoint; pairs from distinct residue classes modulo $2d$ are likewise disjoint. Thus each active step $d$ has a **unique** active centre $x_d$ and forces both pairs $\{x_d - 2d, x_d\}$ and $\{x_d, x_d + 2d\}$ into $F$.
  - If two or more steps are active, their distinct spans give at least four distinct pairwise-intersecting pairs in $F$. Such pairs must share a single point (the only pair avoiding $x$ that meets both $\{x, y\}$ and $\{x, z\}$ is $\{y, z\}$, and no fourth pair can meet all three edges of a triangle). Because the two pairs at step $d$ meet only at $x_d$, all active steps must share the same common centre $x$.
- **Contradiction at the smallest active step $d$:** Both $P = \{x - 2d, x - d, x, x + d, x + 2d\}$ and its middle triple $M = \{x - d, x, x + d\}$ have coefficient $\alpha_{x,d} \ne 0$ and therefore belong to $F$ (the only other $w_{x', d'}$ containing $M$ would use it as the outer triple at step $d/2$, which is inactive or nonintegral by minimality of $d$). Since $\bigcap_{A \in F} A = \varnothing$, choose some $B \in F$ omitting $x$. To intersect the two forced pairs $\{x - 2d, x\}$ and $\{x, x + 2d\}$, $B$ must contain both endpoints $a = x - 2d$ and $b = x + 2d$. The only arithmetic progression inside $P$ containing $a$ and $b$ while omitting $x$ is the pair $\{a, b\}$. Therefore $B \cap P = \{a, b\}$, forcing $B \cap M = \varnothing$—contradiction!

This proves linear independence of the rows in the theorem. $\square$

## Classifying possible seven-term progressions

To turn the rank theorem into a concrete upper bound much sharper than 163, we record which seven-term progressions occur inside $F$. There are **14** seven-term arithmetic progressions in $[16]$ (ten of step $1$ and four of step $2$). Define the **seven-term profile** $S$ of $F$ to be the exact set of seven-term progressions contained in at least one member of $F$.

Knowing the exact profile $S$ imposes two strong structural restrictions on $F$:

1. **Containment condition:** A longer progression ($L \ge 8$) can contribute a positive coordinate to the rank theorem *only if* every seven-term progression contained in it belongs to $S$ (otherwise no member of $F$ can contain that longer progression).
2. **Trace condition:** For every $P \in S$ and every member $A \in F$, the trace $A \cap P$ must be either **empty or an arithmetic progression**. Indeed, by definition of $S$ there is some $B \in F$ with $P \subseteq B$. If $A = B$, then $A \cap P = P$; if $A \ne B$, then $A \cap P = (A \cap B) \cap P$ is an intersection of two progressions, hence empty or a progression.

*Immediate consequences for tiny profiles:*
- If $|S| \le 2$, no progression of length $\ge 9$ can have all its seven-term subprogressions in $S$ (even a nine-term interval contains three seven-term intervals), so the rank bound gives $|F| \le 121 + 2 = 123$.
- If $|S| = 3$, any progression of length $\ge 10$ contains at least four seven-term progressions, so the *only* possible extra coordinate beyond $121 + 3 = 124$ is equality to a nine-term interval—uniquely determined by its three seven-term windows. Thus any 125-member family with $|S| = 3$ must contain that nine-term interval.

## An unconditional upper bound

**Corollary.** The unrestricted maximum on sixteen points satisfies **$124 \le t(16) \le 132$**.

Szabó's construction attains 124, and Yang's theorem bounds every family with a common point by 124 ([Szabó's construction and Yang's starred-family theorem](https://arxiv.org/html/2607.23004v1#S1)). To prove $t(16) \le 132$, it suffices to rule out an admissible family $F$ of **133** members with empty total intersection (any larger family contains a 133-member subfamily). Notice $F$ contains no singleton (which would force a common point).

Furthermore, the separate coloring check at target 130 rules out any family of size 130 whose largest member has size at least 12 ([largest-member proof and verifier](README.md#excluding-large-members)). Since any 133-member family containing a set of size $\ge 12$ would have a 130-member subfamily retaining it, **every member of $F$ has size at most 11**.

Across the $2^{14} = 16{,}384$ subsets of the 14 seven-term progressions, reflection ($i \mapsto 17 - i$) leaves **8,256** canonical seven-term profiles $S$ (the 14 progressions form 7 reflection pairs, so $(2^{14} + 2^7)/2 = 8{,}256$). For each profile $S$, keep the 121 constant and pair coordinates plus only those remaining coordinates whose indexing progression has size at most 11 and all of whose seven-term subprogressions lie in $S$:

- In **6,806** profiles, the total number of surviving coordinates is already less than 133, immediately ruling out $|F| = 133$.
- In the remaining **1,450** profiles, the [C++ verifier](profile_bound.cpp) rules out $|F| = 133$ via the longer-coordinate rank test and compatibility-graph pruning described below.

### The longer coordinates

After accounting for the 121 constant/pair coordinates and the $|S|$ seven-term coordinates, the members of $F$ must still contribute rank at least
$$
q = 133 - 121 - |S|
$$
on the remaining coordinates—call these the **longer coordinates**. A set can have a nonzero entry on the longer coordinates only if it *equals* an interval of length $9, 10,$ or $13$, or *contains* an interval of length $11, 15,$ or $16$.

At target 133, the maximum member size is 11, so any candidate nonzero on the longer coordinates must be a *pure interval* of length $9, 10,$ or $11$ (a set of size $\le 11$ containing an 11-term interval equals that interval). Each such interval has its own unique pivot coordinate, so the rank of any set of longer-coordinate rows is simply the number of distinct rows!

For optional lower targets (where members of size $\ge 12$ may be allowed), the verifier computes the exact longer-coordinate rank using the following general method:

1. **Unique-pivot rows:** Count each present interval of length $9, 10,$ or $13$ once (each has its own equality coordinate). Also count the full 16-term interval and each present 15-term interval once: the 16-term containment coordinate is nonzero *only* on $[16]$, and after eliminating $[16]$ if present, the two 15-term containment coordinates are nonzero *only* on their respective 15-term intervals. All of these rows give independent pivots.
2. **The six 11-term containment coordinates (forest rank):** The only remaining coordinates are containment of the six 11-term intervals $I_1 = [1, 11], \ldots, I_6 = [6, 16]$. Because any two 11-term intervals in $[16]$ overlap, their union is an interval containing every intermediate 11-term interval. Consequently, for any set $A$ containing at least one 11-term interval, the indices $k \in \{1, \ldots, 6\}$ with $I_k \subseteq A$ form a single contiguous interval $[i, j]$.
   - Map any indicator vector $\mathbf{1}_{[i,j]} \in \mathbb{R}^6$ to a vector in $\mathbb{R}^7$ by taking first differences plus the final boundary difference:
     $$
     (x_1, x_2, x_3, x_4, x_5, x_6) \longmapsto (x_1,\, x_2 - x_1,\, x_3 - x_2,\, x_4 - x_3,\, x_5 - x_4,\, x_6 - x_5,\, -x_6).
     $$
     For example, $\mathbf{1}_{[2,4]} = (0, 1, 1, 1, 0, 0) \mapsto (0, 1, 0, 0, -1, 0, 0) = e_2 - e_5$.
   - This linear map is injective (each $x_k$ is recovered as the $k$-th partial sum), so it preserves rank! And every interval indicator $\mathbf{1}_{[i,j]}$ maps to the oriented graph edge vector $e_i - e_{j+1}$ on 7 vertices $\{1, \ldots, 7\}$.
   - Adding an edge $(i, j + 1)$ increases the rank by $1$ precisely when $i$ and $j + 1$ belong to different connected components of the current graph (the oriented edge vectors of a forest are linearly independent, while any edge closing a cycle equals the signed sum of edges along its forest path).

### Eliminating impossible pairs

For each of the 1,450 remaining profiles $S$, build the **compatibility graph** on all candidate subsets satisfying the trace and containment conditions for $S$ (and size $2 \le |A| \le 11$ at target 133), joining two distinct candidates by an edge when their intersection is a nonempty progression. Any hypothetical 133-member family $F$ with profile $S$ is a 133-clique in this graph.

The verifier iteratively deletes vertices and edges that cannot participate in *any* 133-clique (preserving the invariant that every vertex and edge of any hypothetical $F$ survives). Write $N(A)$ for the current neighborhood of $A$. Recall that a proper coloring partitions a vertex set into independent (mutually incompatible) classes, so its number of colors upper-bounds the largest clique in that vertex set. Two verified prerequisites also apply to any 133-member family:

- at least $133 - 121 = 12$ members must be marked ([marked-set proof](rank-mark.md)), and
- at least $133 - 93 = 40$ members must have size at most four ([size bound](five-or-more.md)).

The verifier applies four sound pruning tests:

1. **Seven-term witness and marked-set check on an edge $AB$:** Form the common list of all candidates containing a seven-term progression that are compatible with both $A$ and $B$ (including $A$ and $B$ themselves if they qualify). Every progression in $S$ must have at least one witness on this list, and the list must contain at least 12 marked sets. Otherwise discard $AB$.
2. **Longer-coordinate clique rank check on an edge $AB$:** Restrict the common list to candidates nonzero on the longer coordinates. The actual longer-coordinate members of $F$ form a clique, so they extend to some inclusion-maximal clique of longer-coordinate candidates in the current graph (and intersecting a larger clique with the common list can only increase rank). The verifier enumerates all inclusion-maximal cliques of longer-coordinate candidates; if *none* has rank at least $q = 133 - 121 - |S|$ when intersected with the common list, discard $AB$.
3. **Neighborhood and common-neighborhood coloring checks:**
   - If a proper coloring of $N(A)$ uses fewer than $132$ colors, discard vertex $A$.
   - For an edge $AB$, $N(A) \cap N(B)$ must contain a $131$-clique, its marked candidates must supply $12$ minus any marked endpoints among $\{A, B\}$, and its candidates of size $\le 4$ must supply $40$ minus any endpoints of size $\le 4$. If a proper coloring violates any of these three bounds, discard $AB$. For efficiency, this common-neighborhood test is run on edges that have a longer-coordinate endpoint or two seven-term holders.
4. **Longer-interval survival filter ($q > 0$):** At target 133, $q = 133 - 121 - |S|$ requires at least $q$ of the 9-, 10-, and 11-term intervals to belong to $F$. When $q > 0$, let $L(A)$ be the set of those intervals that are equal or adjacent to $A$ in the current graph. Before coloring $N(A) \cap N(B)$ in Test 3, keep a candidate $C$ only if $|L(A) \cap L(B) \cap L(C)| \ge q$ (and before coloring $N(A)$, keep $C$ only if $|L(A) \cap L(C)| \ge q$), since every member of a valid family containing the chosen endpoints must be compatible with at least $q$ such intervals. Pools sharing the same surviving interval set are cached.

Because every deleted vertex or edge is impossible in any 133-member family, the tests repeat on the reduced graph until convergence. Across all **1,450** profiles, either the surviving vertex count or a final proper coloring drops below 133, completing the proof of $t(16) \le 132$.

## Reproduction

First run the prerequisite [marked-set](rank-mark.md) and [size-at-least-five](five-or-more.md) checks in their linked notes, then run the commands below from this directory using Python 3.10 or later and a C++20 compiler.

The [exhaustive graph verifier](profile_bound.cpp) reads the marked masks from the zero-weight entries of `rank.weights`. By default it checks all 8,256 profiles at the bound $132$ (excluding $133$); an optional first argument sets the upper bound to test, and two optional further arguments select an inclusive range of profile masks.

```sh
python3 signed_rank.py
c++ -std=c++20 -O3 large_members.cpp -o /tmp/erdos272-large
/tmp/erdos272-large 12 130
c++ -std=c++20 -O3 profile_bound.cpp -o /tmp/erdos272-profile-bound
/tmp/erdos272-profile-bound
```
