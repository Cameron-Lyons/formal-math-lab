# A rank bound for families on sixteen points

Let $F$ be a family of at least two distinct subsets of $[16]$ with empty total intersection. Assume any two distinct members meet in a nonempty arithmetic progression. For each $A\in F$, form a row consisting of

- the constant 1,
- the indicators $1_{P\subseteq A}$ for all progressions $P$ of lengths $2,7,11,15,16$,
- the indicators $1_{A=P}$ for all progressions $P$ of lengths $9,10,13$.

**Theorem.** These rows are linearly independent over the reals.

The theorem gives an upper bound of 163 before any coordinates are discarded. It often gives a smaller bound for a prescribed family. In particular, the bound is 121 plus the number of progressions of lengths $7,11,15,16$ contained in at least one member, plus the number of progression members of lengths $9,10,13$.

## Signed count

Give an empty set the weight 1. Give each nonempty progression a weight according to its length.

| Length | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Weight | −1 | 1 | −1 | −1 | 0 | −1 | 1 | −1 | 0 | 0 | 1 | −1 | 0 | −1 | 1 | 1 |

For length $k\ge2$ the table entry is the number-theoretic Möbius function $\mu(k-1)$. To see why these weights give score zero on a progression, fix two of its points at distance $s$ in units of its step. The progressions with those endpoints contribute $\sum_{r\mid s}\mu(r)$, which is 1 for consecutive points and 0 otherwise. The $k-1$ consecutive pairs therefore cancel the constant and the $k$ singleton weights.

Write $q(S)$ for the sum of these weights over the empty set and all progressions contained in $S$. On the 330 nonempty progressions in $[16]$, $q(S)=0$. On the other 65,205 nonempty subsets, $q(S)>0$. The verifier checks each value by summing over subsets. Run `python3 signed_rank.py` from this directory. [Finite score verification](signed_rank.py)

Write $u_A$ and $v_A$ for the containment indicators in $A$ of the positive and negative coordinates, respectively, including the constant in $u_A$. Their inner products satisfy
$$
u_A\cdot u_B-v_A\cdot v_B=q(A\cap B).
$$
Suppose a real linear relation with coefficients $c_A$ holds among the rows of the theorem. The equality coordinates force $c_P=0$ for all progression members of lengths $9,10,13$. Since the distinct-member intersections have score zero, squaring the relation on its positive containment coordinates gives
$$
0=\Big\|\sum_{A\in F} c_A v_A\Big\|^2+\sum_{A\in F} c_A^2 q(A).
$$
Hence all non-progression coefficients vanish, and the negative containment coordinates also satisfy the relation. Extend $c$ by zero to all progressions outside the family.

## The five-term relations

For a five-term progression $P$ of step $d$ and centre $x$, write $a=x-2d$, $b=x+2d$, and $O=\{a,x,b\}$. In the coefficient space with unit vectors $e_D$ put
$$
 h(D)=e_D-e_{D\setminus\{a\}}-e_{D\setminus\{b\}}+
 e_{D\setminus\{a,b\}},\qquad w_{x,d}=h(P)-h(O).
$$
Evaluating $h(D)$ on a containment coordinate $T$ gives 1 exactly when $\{a,b\}\subseteq T\subseteq D$. The only progressions in $P$ containing both endpoints are $\{a,b\},O,P$. Therefore $w_{x,d}$ vanishes on all positive and negative containment coordinates, since the five-term coordinate has weight zero. Its only five-term coefficient is 1 at $P$.

Subtract $c_P w_{x,d}$ from the relation for each such $P$. Every remaining progression with a possibly nonzero coefficient indexes its own containment coordinate. Taking an inclusion-maximal one would make that coordinate nonzero. Thus $c=\sum_{x,d}\alpha_{x,d}w_{x,d}$, where $\alpha_{x,d}=c_P$.

Fix $d$ with an active centre, meaning one with $\alpha_{x,d}\ne0$. The coefficient of the pair $\{u,u+2d\}$ is $\alpha_{u,d}+\alpha_{u+2d,d}$, taking unavailable centres to have coefficient zero. In each active residue class modulo $2d$, its first and last active centres $p,q$ force both pairs $\{p-2d,p\}$ and $\{q,q+2d\}$ into $F$. If $p<q$, these pairs are disjoint. Pairs from distinct residue classes are also disjoint. Hence each active step has precisely one active centre and forces its two pairs. With two or more steps this gives at least four distinct pairwise intersecting pairs. Such pairs share a point, since the only pair meeting both $\{x,y\}$ and $\{x,z\}$ but missing $x$ is $\{y,z\}$, and a triangle admits no fourth pair meeting all three. Consequently all active steps have the same centre $x$.

Take the smallest active step $d$. Both its five-term $P$ and its middle triple $M=\{x-d,x,x+d\}$ have coefficient $\alpha_{x,d}\ne0$. The only other possible contribution to $M$ would be from the outer triple of step $d/2$, which is inactive or unavailable. As $F$ has empty total intersection, some $B\in F$ omits $x$. It must contain $a,b$ to meet the two forced pairs. The only progression in $P$ containing $a,b$ and omitting $x$ is their pair. Hence $B\cap M$ is empty. This contradiction proves independence.

## Classifying possible seven-term progressions

Let $S$ contain exactly the seven-term progressions that lie in some family member. A longer progression can contribute a coordinate only if all its seven-term subprogressions belong to $S$. Also, for every $P\in S$ and $A\in F$, the trace $A\cap P$ is empty or a progression. Indeed, choose $B\in F$ containing $P$. For $A=B$ the trace is $P$, and otherwise it equals the intersection of $P$ with the progression $A\cap B$. A nonempty intersection of progressions is a progression.

In particular, when $|S|\le2$ there are at most 123 rows. For $|S|=3$, the only possible additional coordinate after the first $121+3$ is equality to a nine-term interval, since any longer progression in $[16]$ contains at least four seven-term progressions. A nine-term interval is uniquely determined by its three seven-term windows. Thus a family of size 125 in this case must contain the nine-term interval giving those windows.

## An unconditional upper bound

**Corollary.** The unrestricted maximum on sixteen points satisfies $124\le t(16)\le132$.

Szabó's construction attains 124, and Yang bounds every family with a common point by 124. It remains to exclude a family $F$ of exactly 133 members and empty total intersection. A larger family would contain a subfamily of this size. A singleton cannot belong to $F$, as its point would belong to every member. [Szabó's construction and Yang's starred-family theorem](https://arxiv.org/html/2607.23004v1#S1)

A separate coloring check excludes families of size 130 whose largest member has size at least twelve. Any 133-member family containing such a member would have a 130-member subfamily retaining it. Hence every candidate has size at most eleven. [Largest-member proof and verifier](README.md#excluding-large-members)

For an exact seven-term profile $S$, allow the 121 constant and pair coordinates. Allow each remaining coordinate only if its index has at most eleven points and all its seven-term subprogressions belong to $S$. Reflection gives 8,256 classes among the $2^{14}$ profiles. In 6,806 classes the resulting dimension is less than 133. The verifier excludes the other 1,450 using the graph described below.

### The longer coordinates

After allowing the 121 constant and pair coordinates and the $|S|$ seven-term coordinates, the rows of $F$ must still have rank at least $133-121-|S|$ on their remaining coordinates. Call these the longer coordinates. A set can contribute here only if it equals an interval of length 9, 10 or 13, or contains an interval of length 11, 15 or 16.

At this target the size restriction makes each nonzero longer row a pure interval of length 9, 10 or 11. Each such row has its own pivot. The number of distinct longer rows is therefore their rank. For the optional lower targets, the verifier uses the following general calculation. First count each of its intervals of lengths 9, 10 and 13 once. Each has its own equality coordinate. Count the 15-term intervals and the 16-term interval once each as well. The 16-term containment coordinate occurs only on the full interval. After eliminating that row if present, the two 15-term coordinates occur only on their own intervals. These rows contribute independent pivots.

Only the six 11-term containment coordinates can remain nonzero. For a given set, the starts of the 11-term intervals it contains form a single interval of indices, because any two 11-term intervals in $[16]$ overlap, so the set contains their union. Map the indicator of an interval of indices $[i,j]$ to the vector $e_i-e_{j+1}$ in seven positions by taking first differences and adding the final boundary difference. This linear map is injective. For each nonzero row add an edge from $i$ to $j+1$. Its rank contribution is 1 exactly when the edge joins two previously separate components. Indeed the oriented edge vectors of a forest are independent, and the vector of any additional edge is the signed sum along its forest path.

### Eliminating impossible pairs

For each remaining profile, form the candidate list using the two trace and containment conditions in the previous section. Join two distinct candidates when their intersection is a nonempty progression. The verifier maintains a graph that retains every vertex and every edge of any hypothetical $F$. Write $N(A)$ for the current neighbors of $A$. A proper coloring partitions vertices into classes of mutually nonadjacent candidates, so its number of colors bounds the size of any clique.

The marked-set certificate requires at least $133-121=12$ marked members in $F$. The bound of 93 for a subfamily whose members all have size at least five requires at least $133-93=40$ members of size at most four. [Marked-set proof](rank-mark.md) · [Size bound](five-or-more.md)

The following tests preserve the graph invariant.

1. For an edge $AB$, list all seven-term progression holders compatible with both endpoints, allowing an endpoint itself in this list. Every progression in $S$ needs a witness on the list, and the list must contain at least 12 marked sets.
2. Restrict that common list to candidates contributing on the longer coordinates. The actual longer-coordinate members must form a clique. The verifier enumerates maximal cliques of the longer-coordinate candidates in the current graph. At least one of these cliques, intersected with the common list, must have rank at least $133-121-|S|$ by the preceding calculation. Otherwise discard $AB$.
3. If a coloring of $N(A)$ has fewer than 132 colors, discard $A$. If $A,B\in F$, then $N(A)\cap N(B)$ must contain a clique of size 131. Within the common neighborhood the marked candidates must supply the 12 required marked members less any marked endpoints. The candidates of size at most four must likewise supply 40 less any such endpoints. A coloring that fails any of these bounds discards $AB$. For efficiency the verifier applies the common-neighborhood colorings only to edges with a longer-coordinate endpoint or with two seven-term holders.

4. Let $q=133-121-|S|$. At least $q$ of the 9-, 10- and 11-term intervals must belong to $F$. When $q>0$, write $L(A)$ for the possible intervals equal or adjacent to $A$ in the current graph. Before coloring a common neighborhood in test 3, retain a candidate $C$ only if $|L(A)\cap L(B)\cap L(C)|\ge q$. For a single-vertex neighborhood, use $|L(A)\cap L(C)|\ge q$. Every member of a hypothetical family containing the chosen endpoints must pass. The implementation caches pools with the same possible interval set.

Each rejected edge or vertex is excluded from every hypothetical 133-member family, so the tests may be repeated on the reduced graph. The final vertex count or a final proper coloring excludes such a family in all 1,450 profiles. The verifier uses inclusion-maximal cliques of the longer-coordinate candidates in test 2. Every clique extends to one, and the rank of its intersection with a fixed list can only increase on extension.

Run the marked-set and size-at-least-five checks in their linked notes, then run the following commands in this directory with Python 3.10 or later and a C++20 compiler. The graph verifier reads the marked masks from the zero weights in `rank.weights`. Its default run checks all 8,256 profiles. An optional first argument selects the upper bound to test, and two further arguments select an inclusive range of profile masks. [Exhaustive graph verifier](profile_bound.cpp)

```sh
python3 signed_rank.py
c++ -std=c++20 -O3 large_members.cpp -o /tmp/erdos272-large
/tmp/erdos272-large 12 130
c++ -std=c++20 -O3 profile_bound.cpp -o /tmp/erdos272-profile-bound
/tmp/erdos272-profile-bound
```
