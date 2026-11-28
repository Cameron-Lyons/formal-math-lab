# Arithmetic-progression intersections on sixteen points

How many distinct subsets of $\{1, 2, \ldots, 16\}$ can you collect so that every two distinct subsets intersect in a nonempty arithmetic progression? Singletons (such as $\{8\}$) and pairs (such as $\{2, 11\}$) count as arithmetic progressions of length one and two. Write $t(16)$ for the largest possible size of such a family—also called an *admissible* (or *AP-intersecting*) family—on $[16] = \{1, \ldots, 16\}$.

**The verified unrestricted bounds are $124 \le t(16) \le 132$.** The lower bound comes from Szabó's construction, which is kernel-verified in Lean here. Yang proved that 124 is the exact maximum among *starred* families (those in which all members share a common point). The upper bound of 132 established here removes that restriction and also covers families with *empty total intersection* ($\bigcap_{A \in F} A = \varnothing$). Whether an unrestricted family can reach 125 remains open in this calculation.

[Szabó, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) · [Yang, Theorems 1.2 and 1.4](https://arxiv.org/abs/2607.23004) · [Unrestricted upper bound and verification](signed-rank.md)

## At a glance

| Result | Bound / Status | Method & Proof | Verifier |
| --- | --- | --- | --- |
| Lower bound on $t(16)$ | $t(16) \ge 124$ | Szabó's construction (intersections $\le 4$ terms) | [Erdos272Sixteen.lean](Erdos272Sixteen.lean) |
| Unrestricted upper bound | $t(16) \le 132$ | Möbius signed rank + 7-term profile graph pruning | [signed-rank.md](signed-rank.md) · [profile_bound.cpp](profile_bound.cpp) |
| Intersections $\le 6$ terms on $[16]$ | Exact max $= 124$ | Signed rank (101 marks) + 6,129 quartet checks | [short-intersections.md](short-intersections.md) · [verify_short.py](verify_short.py) |
| Intersections $\le 5$ terms on $[N]$ | Exact max $= 1 + \binom{N}{2} + \lfloor (N-1)/4 \rfloor$ | Signed rank + 5-term inclusion–exclusion relations | [seven-term-intersections.md](seven-term-intersections.md#exact-maximum-when-intersections-have-at-most-five-terms) |
| Infrequent omissions on $[N]$ and $[16]$ | $\le 13$ omissions on $[16] \implies \lvert F \rvert \le 124$ | Replacement into starred bound + finite check | [general-bound.md](general-bound.md) · [verify_near.py](verify_near.py) |
| Size-restricted subfamilies on $[16]$ | Size $\ge 5$: $\le 93$; size $\ge 4$: $\le 123$ | Private nonprogression triples + color classes | [five-or-more.md](five-or-more.md) · [four-or-more.md](four-or-more.md) |
| Direct search at 125 members | 91 of 426 root cases excluded (335 open) | Private-triple elimination + large-member bound | [small-root-search.md](small-root-search.md) |

## The family of 124

Szabó's construction builds a 124-member family in which every member contains the point $8$:

1. **Start with a star of small sets:** Take all $1 + 15 + \binom{15}{2} = 121$ subsets of $[16]$ of size at most three that contain $8$. Any two of these meet in $8$ plus at most one other point, so every pairwise intersection has size one or two (automatically a progression).
2. **Swap triples for longer progressions at steps $d = 1, 2, 3$:** For each $d \in \{1, 2, 3\}$, consider the five-term progression $P_d = \{8 - 2d, 8 - d, 8, 8 + d, 8 + 2d\}$ centred at $8$—namely $\{6, 7, 8, 9, 10\}$, $\{4, 6, 8, 10, 12\}$, and $\{2, 5, 8, 11, 14\}$.
   - **Remove** the two *nonprogression triples* inside $P_d$ that pass through $8$ (for instance, $\{6, 8, 9\}$ and $\{7, 8, 10\}$ when $d = 1$, whose gaps are unequal). Keeping them would produce nonprogression intersections with $P_d$.
   - **Add** $P_d$ itself together with its two four-term subprogressions obtained by dropping an endpoint (for $d = 1$, these are $\{6, 7, 8, 9\}$ and $\{7, 8, 9, 10\}$).

Each step $d$ removes 2 sets and adds 3, giving $121 - 6 + 9 = 124$ members in total. Lean (`decide +kernel`) checks that all 124 sets are distinct and verifies that all $\binom{124}{2} = 7{,}626$ pairwise intersections are nonempty arithmetic progressions of at most four terms. [Lean theorem](Erdos272Sixteen.lean)

## What a family of 125 would require

To prove $t(16) = 124$, one must rule out a family of 125 subsets with empty total intersection (any larger family contains a 125-member subfamily, and Yang's bound already rules out families with a common point). The proofs in this directory pin down strong structural properties that any hypothetical 125-member family must satisfy:

- **Every point is omitted at least 14 times.** Equivalently, every point of a 125-member family occurs in at most 111 sets. The same degree cap of 111 holds for any larger family as well: picking 112 sets through a single point and extending them to a 125-member subfamily would leave at most 13 omissions of that point. [Omission bound and finite verifier](general-bound.md)
- **At least 32 members have size at most four.** The subfamily of sets of size at least five has size at most 93. The proof charges each nonprogression set for its *private* nonprogression triples (triples whose arithmetic-progression hull is not contained in the set) and checks 56 cases indexed by a longest progression member. [Counting proof and verifier](five-or-more.md)
- **At least ten members are nonprogression triples.** A *nonprogression triple* is a three-element set with unequal successive gaps, such as $\{1, 2, 4\}$ (gaps $1$ and $2$). Because the triple itself is not a progression, every other family member must meet it in exactly one or two points. Deleting all nonprogression triples from any family of size at least 125 leaves at most 115 members. Moreover, some pair of ground points intersects every member of size at most three. [Four-element bound](four-or-more.md) · [Nonprogression-triple proof](nonprogression-triples.md)
- **Both endpoints occur as singleton intersections.** At $1$ (and symmetrically at $16$), at least three disjoint pairs of family members—six distinct sets—intersect in just $\{1\}$. [Endpoint proof and verifier](endpoint.md)
- **At least four members belong to a specific list of 363 "marked" subsets.** Using a signed-rank matrix with integer diagonal-dominance weights, the remaining unmarked members have linearly independent incidence vectors on the constant coordinate and the 120 pairs (dimension 121), forcing at least $125 - 121 = 4$ marked members. The verifier constructs the 363-set list from integer weights and checks every required inequality. [Rank certificate](rank-mark.md)
- **Every member has at most twelve elements.** Fixing a largest member $A$ and forming the compatibility graph of all its possible companions, repeated proper-coloring bounds exclude every choice of a largest member of size 13 through 16. [Large-member check](#excluding-large-members)

### Intersection lengths and the upper bound of 132

- **Exact maximum for intersections of at most six terms:** When every pairwise intersection has at most six terms, the exact maximum on $[16]$ is **124**. The signed-rank method isolates 101 marked sets and reduces the problem to 6,129 canonical choices of the first four marked sets, all excluded by the private-triple count. [Short-intersection proof](short-intersections.md)
- **No eleven-term intersections:** A separate graph search rules out any pair of members intersecting in an eleven-term progression. Combined with the size cap of 12 (two distinct sets of size $\le 12$ cannot share 12 points), the longest pairwise intersection in any hypothetical 125-member family must have between **seven and ten terms**. [Eleven-term check](#excluding-eleven-term-intersections)
- **Seven-term profiles and the bound $t(16) \le 132$:** There are 14 seven-term arithmetic progressions in $[16]$. Recording which subset of them appears inside at least one family member gives a *seven-term profile*; up to reflection ($i \mapsto 17 - i$), there are 8,256 possible profiles. To rule out 133 members (proving $t(16) \le 132$), the Möbius signed-rank dimension immediately excludes 6,806 profiles, and compatibility-graph pruning excludes the remaining 1,450. The verifier's optional first argument sets the target upper bound to test, so lower targets down to the conjectured value 124 can also be tested one profile range at a time. [Search proof and run totals](signed-rank.md) · [C++ verifier](profile_bound.cpp)
- **Direct root search at 125 members:** Partitioning hypothetical 125-member families into 426 cases defined by specific marked root members, the private-triple search and large-member bound exclude 91 cases (78 by private-triple elimination and 13 by size $\ge 13$), leaving 335 cases open. [Method and replay commands](small-root-search.md)

## Results for general ground sets

Several arguments developed for $N = 16$ work on $[N] = \{1, \ldots, N\}$ for arbitrary $N$:

- **Exact maximum for intersections of at most five terms:** For every $N \ge 1$, if all pairwise intersections have at most five terms, the exact maximum family size is $1 + \binom{N}{2} + \lfloor (N - 1)/4 \rfloor$ (with no limit on the sizes of the family members themselves). Stronger still: inside *any* admissible family with empty total intersection, any subfamily whose pairwise intersections have at most five terms has size at most $1 + \binom{N}{2}$. On sixteen points ($1 + \binom{16}{2} = 121$), this implies that any 125-member family must contain two disjoint pairs of members whose intersections have at least six terms. [Proof](seven-term-intersections.md#exact-maximum-when-intersections-have-at-most-five-terms)
- **Infrequent omissions of a point:** Set $k = \lfloor (N - 1)/4 \rfloor$. For every positive $N$, if some point is omitted by at most $k + 1 + \lceil 2\sqrt{k + 1} \rceil$ members, then $|F| \le 1 + \binom{N}{2} + k$. This improves the earlier replacement bound of $k + 1$ omissions by bounding how many distinct omitted members can extend their common intersection interval. For $k \ge 7$, adjoining disjoint three-term progressions raises the threshold further to $k + 1 + \lceil \frac{4}{3}\sqrt{3k - 1} \rceil$—for example, at $N = 100$ ($k = 24$), the threshold rises from 25 omissions to 37. [Proof](general-bound.md)
- **Intersections of at most seven terms:** When every pairwise intersection has at most seven terms and the total intersection is empty, let $t$ count the distinct six- or seven-term progressions that actually occur as pairwise intersections; then $|F| \le 1 + \binom{N}{2} + 2t$. There is also a linear-algebraic bound $|F| \le 1 + \binom{N}{2} + \operatorname{rank}_{\mathbb{R}} M$ using the incidence matrix $M$ of members against seven-term progressions. [Proofs](seven-term-intersections.md)
- **Prime-grid signed-rank theorem:** An incidence construction based on prime subdivisions of intervals produces linearly independent real vectors for any family with empty total intersection on *any* finite set of integers, with a diagonal score that counts endpoint pairs admitting no common prime subdivision and is strictly positive on every nonprogression. [Prime-grid rank theorem](prime-grids.md)

## Reproduce

Run the following commands from this directory using Lean 4.36.0, Python 3.10 or later, and a C++20 compiler:

```sh
lake --wfail build
lake env leanchecker --fresh Erdos272Sixteen
python3 signed_rank.py
c++ -O2 -std=c++20 five_or_more.cpp -o /tmp/erdos272-five16
/tmp/erdos272-five16
c++ -O2 -std=c++20 rank_mark.cpp -o /tmp/erdos272-rank16
/tmp/erdos272-rank16 rank.weights
c++ -O3 -std=c++20 large_members.cpp -o /tmp/erdos272-large
/tmp/erdos272-large 12 130
c++ -O3 -std=c++20 profile_bound.cpp -o /tmp/erdos272-profile16
/tmp/erdos272-profile16 132
```

The linked proof notes give the additional commands for the omission, endpoint, small-member, and short-intersection checks.

### Excluding large members

**Claim.** Every member of an admissible family of at least 125 subsets of $[16]$ has size at most 12. Every member of an admissible family of at least 130 subsets has size at most 11.

**The big idea.** Fix a largest member $A$ of a hypothetical 125-member family. Every other member must fit inside the *compatibility graph* of sets compatible with $A$, where two candidates are joined by an edge if they intersect in a nonempty arithmetic progression. The remaining 124 members form a 124-clique in this graph. Because any *proper coloring* of a graph partitions its vertices into independent sets (each of which can contribute at most one vertex to a clique), the number of colors upper-bounds the clique number. We repeatedly prune vertices and edges whose neighborhoods cannot support a large enough clique until nothing survives.

**Details.** Identify $A$ with its reflection $i \mapsto 17 - i$. No member can be a singleton, because a singleton would force the entire family to share its unique point (contradicting Yang's bound of 124). The other 124 members therefore form a clique in the compatibility graph whose vertices are all subsets $B \ne A$ satisfying $2 \le |B| \le |A|$ such that $A \cap B$ is a nonempty progression, with an edge between distinct $B_1, B_2$ whenever $B_1 \cap B_2$ is a nonempty progression.

The verifier applies two sound deletion rules:

1. **Vertex pruning:** Discard a vertex $B$ if a proper coloring of its neighborhood uses fewer than 123 colors (so $B$ cannot belong to any 124-clique).
2. **Edge pruning:** Discard an edge $B_1 B_2$ if a proper coloring of their common neighborhood uses fewer than 122 colors (so $B_1$ and $B_2$ cannot both belong to a 124-clique). For speed, the verifier applies this edge test to pairs of candidates of size at most three.

Because every deletion preserves all 124-cliques, the tests can be iterated on the shrinking graph. They exclude all 1, 8, 64, and 280 reflection classes of a largest member $A$ of sizes 16, 15, 14, and 13, respectively. The same maximum size of 12 applies to any family larger than 125: retain a largest member and extend it to a 125-member subfamily.

At a target family size of 130, the exact same coloring tests also exclude all 924 reflection classes of size 12. Hence every admissible family of at least 130 members has maximum member size at most 11. [Large-member verifier](large_members.cpp) · [Shared graph checks](compatibility_graph.hpp)

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic large_members.cpp -o /tmp/erdos272-large
/tmp/erdos272-large
/tmp/erdos272-large 12 130
```

### Excluding eleven-term intersections

**Claim.** No two distinct members of an admissible family of at least 125 subsets of $[16]$ intersect in an arithmetic progression of eleven or more terms.

**Why this reduces to 45 cases.** Suppose distinct members $A, B$ of a 125-member family intersect in an eleven-term progression $P$. By the large-member bound above, $|A|, |B| \le 12$. (This also immediately rules out twelve-term intersections, since two distinct sets of size at most 12 cannot share 12 elements.)

In $[16]$, an eleven-term progression must have step $1$ (step $2$ would require span $20 > 15$), so $P$ is one of the 6 intervals of length 11 ($[1, 11]$ through $[6, 16]$). Write $A = P \cup X$ and $B = P \cup Y$, where $X, Y \subseteq [16] \setminus P$ are disjoint sets of size at most $1$, not both empty. Outside $P$ there are 5 points, so the unordered pair $\{X, Y\}$ consists either of the empty set and one of 5 singletons (5 choices), or of two distinct singletons ($\binom{5}{2} = 10$ choices). Reflection pairs the 6 intervals into 3 orbits, leaving
$$
\frac{6\left(5 + \binom{5}{2}\right)}{2} = 45
$$
canonical cases to check.

**Candidate filtering and coloring tests.** Every other member $C$ of the family must intersect each of $A$ and $B$ in a nonempty progression. Its trace $C \cap P = (C \cap A) \cap (C \cap B)$ is the intersection of two progressions, hence is either empty or a progression itself.

Each of the 45 cases requires 123 additional mutually compatible members. The verifier runs the same iterative vertex and edge coloring checks as in the large-member calculation, strengthened with three pool requirements (each adjusted by subtracting any fixed members already belonging to that pool):

- **Omission pools:** For every point $x \in [16]$, the members omitting $x$ must supply at least 14 sets in total ([omission bound](general-bound.md)).
- **Size $\le 4$ pool:** Members of size at most four must supply at least 32 sets ([five-element bound](five-or-more.md)).
- **Size $\le 3$ pool:** Members of size at most three must supply at least 10 sets ([small-member bounds](nonprogression-triples.md)).

If a case still survives after pruning, the verifier branches by fixing a nonprogression triple from the surviving vertices—at least one must occur in any 125-member family—and re-runs the same tests with 122 additional members required. These checks exclude all 45 cases. The exclusion extends to any family larger than 125 by taking a 125-member subfamily that contains any given pair. [Verifier](long_intersections.cpp) · [Omission bound](general-bound.md) · [Small-member bounds](nonprogression-triples.md)

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic long_intersections.cpp -o /tmp/erdos272-long
/tmp/erdos272-long
```
