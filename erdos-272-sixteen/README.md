# Arithmetic-progression intersections on sixteen points

Let $t(16)$ be the largest size of a family of distinct subsets of $\{1,\ldots,16\}$ in which every two distinct members intersect in a nonempty arithmetic progression. Singletons and pairs count as progressions.

**The verified unrestricted bounds are $124\le t(16)\le132$.** The lower bound is Szabó's construction. Yang proved that 124 is optimal among families with a common point. The upper bound here also covers families with empty total intersection. Whether such a family can reach 125 remains open in this calculation. [Szabó, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) · [Yang, Theorems 1.2 and 1.4](https://arxiv.org/abs/2607.23004) · [Unrestricted upper bound and verification](signed-rank.md)

## The family of 124

Start with all 121 sets of size at most three containing 8. For each $d=1,2,3$ consider the five-term progression centred at 8 with step $d$. Remove its two nonprogression triples through 8, and add the progression and the two four-term progressions obtained by removing an endpoint. The result has $121-6+9=124$ members. Lean checks distinctness and verifies that all $\binom{124}{2}=7{,}626$ pairwise intersections are progressions of at most four terms. [Lean theorem](Erdos272Sixteen.lean)

## What a family of 125 would require

- **Every point is omitted at least 14 times.** Equivalently, every point of a 125-member family occurs in at most 111 sets. In a larger family, choosing 112 sets through one point and extending them to 125 would give at most 13 omissions, so the same degree bound holds. [Omission bound and finite verifier](general-bound.md)
- **At least 32 members have size at most four.** The subfamily of sets of size at least five has size at most 93. The argument counts nonprogression triples and checks 56 cases according to a longest progression member. [Counting proof and verifier](five-or-more.md)
- **At least ten members are nonprogression triples.** These are three-element sets with unequal successive gaps. Every other member must meet each such triple in one or two points. After deleting all such triples from a family of size at least 125, at most 115 members remain. Some pair of ground points meets every member of size at most three. [Four-element bound](four-or-more.md) · [Nonprogression-triple proof](nonprogression-triples.md)
- **Deleting an endpoint creates at most eleven duplicate pairs.** If the unrestricted maximum on fifteen points is 109, then three disjoint pairs of members in a 125-member family must intersect in exactly that endpoint. [Endpoint proof and verifier](endpoint.md)
- **At least four members belong to a specific list of 363 subsets.** The remaining members have linearly independent incidence vectors on the constant and the 120 pairs. The verifier constructs the list from integer weights and checks every necessary inequality. [Rank certificate](rank-mark.md)
- **Every member has at most twelve elements.** Fix a largest member and form the graph of all its possible companions. The graph search excludes every choice of a largest member of size 13 through 16. [Large-member check](#excluding-large-members)

**When every pairwise intersection has at most six terms, the exact maximum is 124.** The upper bound reduces to 6,129 choices of four marked sets. The same private-triple count excludes all of them. A separate search excludes eleven-term intersections as well. Thus the longest intersection in a family of 125 would have between seven and ten terms. [Short-intersection proof](short-intersections.md) · [Eleven-term check](#excluding-eleven-term-intersections)

There are fourteen seven-term progressions in $[16]$. Recording which of them are contained in a member gives 8,256 possible choices up to reflection. For the unrestricted upper bound of 132, rank excludes 6,806 choices and graph pruning excludes the remaining 1,450. Its optional first argument sets the upper bound to test, so the conjectured value can also be tested one range at a time. [Search proof and run totals](signed-rank.md) · [C++ verifier](profile_bound.cpp)

At the conjectured value, the search for 125 members excludes 91 of 426 cases defined by specific marked members. The ledger records the other 335 cases for resumption. [Method and replay commands](small-root-search.md) · [Case ledger](full-root-status.txt)

## Results for general ground sets

**If all pairwise intersections have at most five terms, the exact maximum for every $N$ is $1+\binom N2+\lfloor(N-1)/4\rfloor$.** The sets in the family may be arbitrarily large. More generally, within a family with empty total intersection, any subfamily satisfying this length restriction has at most $1+\binom N2$ members. Thus on sixteen points, any family of 125 would need two disjoint pairs of members whose intersections have at least six terms. [Proof](seven-term-intersections.md#exact-maximum-when-intersections-have-at-most-five-terms)

Put $k=\lfloor(N-1)/4\rfloor$. For every positive $N$, if some point is omitted by at most $k+1+\lceil2\sqrt{k+1}\rceil$ members, the family has size at most $1+\binom N2+k$. The earlier replacement argument covered $k+1$ omissions. The proof counts how many different omitted sets can extend their common interval. An additional triple count strengthens the result for $k\ge7$. For example, at $N=100$ the threshold rises from 25 omissions to 37. [Proof](general-bound.md)

When every intersection has at most seven terms, let $t$ count the distinct six- or seven-term progressions actually occurring as intersections. A family with empty total intersection then has at most $1+\binom N2+2t$ members. There is also a bound using the rank of the seven-term progression incidence matrix. [Proofs](seven-term-intersections.md)

An incidence construction using prime subdivisions gives linearly independent vectors on any finite integer ground set. Its score counts pairs of endpoints with no common prime subdivision and is strictly positive on every nonprogression. [Prime-grid rank theorem](prime-grids.md)

## Reproduce

Run from this directory with Lean 4.36.0, Python 3.10 or later, and a C++20 compiler.

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

The linked proofs give the additional commands for the omission, endpoint, small-member and short-intersection checks.

### Excluding large members

Choose a largest member $A$ of a hypothetical family of 125, identifying $A$ with its reflection. A singleton would force the entire family to share a point. The other 124 members must therefore belong to the graph on subsets $B\ne A$ with $2\le |B|\le |A|$ and $A\cap B$ a nonempty progression. Join two distinct candidates when they intersect in a nonempty progression.

A partition of a candidate list into independent color classes bounds the largest clique by the number of colors. Discard a vertex if its neighborhood cannot supply a clique of 123 more vertices. For an edge, discard it if its common neighborhood cannot supply 122 more. The verifier applies the edge test to pairs of candidates of size at most three. These deletions preserve every 124-clique, so the checks can be repeated on the smaller graph. They exclude all 1, 8, 64 and 280 reflection classes with largest member of sizes 16, 15, 14 and 13 respectively. The same size limit holds for larger families, by retaining a largest member in a 125-member subfamily. At a target of 130 members, the coloring tests exclude all 924 reflection classes of size twelve as well. Hence every family of at least 130 would have maximum member size eleven or less. [Large-member verifier](large_members.cpp) · [Shared graph checks](compatibility_graph.hpp)

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic large_members.cpp -o /tmp/erdos272-large
/tmp/erdos272-large
/tmp/erdos272-large 12 130
```

### Excluding eleven-term intersections

Suppose members $A,B$ of a 125-member family intersect in an eleven-term progression $P$. They each have size at most twelve. Enumerate the disjoint sets $X,Y$ outside $P$ with $A=P\cup X$ and $B=P\cup Y$, allowing either extension to be empty. There are six possible intervals $P$. For each, the unordered pair of extensions consists of the empty set and one of five singletons, or two distinct singletons. Reflection pairs the six intervals, leaving $6(5+\binom52)/2=45$ cases. Every other member must intersect each of $A,B$ in a nonempty progression. Its trace on $P$ is the intersection of those two progressions, hence is empty or a progression.

Each choice needs 123 more members. Use the same vertex and edge coloring tests as in the large-member calculation. The members omitting any given point must supply 14 in total. The members of size at most four must supply 32, and those of size at most three must supply ten. Subtract any contributions of fixed members before coloring these pools. If a case survives, select a nonprogression triple from the surviving vertices. One must occur. Apply the same tests again with the triple fixed and 122 more members required. These checks exclude all 45 choices. Two distinct sets of size at most twelve cannot intersect in twelve points, so every intersection has at most ten terms. The result extends to larger families by taking a 125-member subfamily containing any given pair. [Verifier](long_intersections.cpp) · [Omission bound](general-bound.md) · [Small-member bounds](nonprogression-triples.md)

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic long_intersections.cpp -o /tmp/erdos272-long
/tmp/erdos272-long
```
