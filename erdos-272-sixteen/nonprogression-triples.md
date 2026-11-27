# Nonprogression triples are necessary

Every admissible family of $k\ge125$ subsets of $[16]$ has **at least $k-115$ three-element members whose gaps are unequal**. In particular, a 125-member family needs at least ten nonprogression triples. Every other member meets each such triple in one or two points.

## Finding the first nonprogression triple

An admissible family with no nonprogression triple among its members has at most 124 members.

Suppose instead that a family of 125 members contained no nonprogression triple. Yang's bound rules out a common point and therefore rules out singleton members. The available sets are all pairs, all 56 three-term progressions, and all sets with four or more elements. At most 93 members have size at least five, so the family needs at least 32 members of size at most four. The rank certificate forces at least four marked members. [Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004) · [Five-element bound](five-or-more.md) · [Marked-set bound](rank-mark.md)

The [small-member elimination argument](four-or-more.md) now applies to the expanded list of possible members. If a marked member has size at least eight, fix a marked member of maximum size, giving 178 cases up to reflection. Otherwise the four marks are distinct seven-term progressions. Up to reflection they have 248 possible pairwise-compatible choices. In each case, successively test the remaining pairs, three-term progressions, and four-element sets as possible members. The triple budget and the incompatible classes give an upper bound after each choice. Each time the bound is below 125, that set can be removed. The case closes once the root bound is below 125 or too few small candidates remain. If an additional marked member is needed, the verifier branches as in the four-element proof.

## Sizes of the remaining members

If an admissible family contains a nonprogression triple $T$, it has at most 115 members of size at least four. Fix $T$ and suppose the subfamily with at least four elements had size 116. The five-element bound requires at least $116-93=23$ four-element members. All candidates meet $T$ in exactly one or two points. In the four-element elimination proof, use only private triples that meet $T$, and remove $T$ itself from the budget. A remaining candidate cannot contain $T$. When a four-element member $S$ is temporarily fixed, price only triples meeting both $T$ and $S$. The fixed external triple $T$ does not count towards the threshold of 116. All 252 choices of $T$ up to reflection close. This calculation uses the five-element bound and does not require a rank certificate. [Elimination proof](four-or-more.md#excluding-four-element-candidates)

Combining the two results, a family of size $k\ge125$ contains at least $k-115$ members of size at most three. In particular, it needs at least ten such members at size 125.

## Counting nonprogression triples

Let $F$ have $k\ge125$ members and remove every nonprogression triple to obtain $R$. Since $F$ contains at least one such triple, it has at most 115 members of size at least four. It also has no singleton, by Yang's bound. If $|R|\ge116$, then $R$ contains a pair or a three-term progression $S$. Fix $S$ and choose 116 members of $R$ including $S$.

There are 64 choices of the pair and 28 choices of the progression up to reflection. For each choice the checker allows every other pair, three-term progression and set of size at least four meeting $S$ in a nonempty progression. The 93-member bound for sets of size at least five forces at least 23 members of size at most four, including $S$. It applies the private-triple bound to the whole candidate list and to the subfamily with at least five elements, which can increase the number of small members required. It then successively eliminates small candidates whose inclusion violates the private-triple bound or leaves too few mutually compatible small candidates. A color class consists of mutually incompatible candidates, and hence contains at most one family member. All 92 cases close. Thus $|R|\le115$ and $|F\setminus R|\ge k-115$. This last computation uses no marked-member or long-intersection restrictions. [Private-triple bound](four-or-more.md#excluding-four-element-candidates) · [Small-member search](small_root_search.cpp)

## When the largest marked members have seven elements

Suppose a 125-member family has no marked member larger than seven. It then has at least five nonprogression triples. Indeed, removing all its nonprogression triples leaves all four required marked members intact. These are four distinct seven-term progressions. In each of their 248 cases the same elimination bounds this remaining subfamily by 120. Subtracting from 125 gives the claim. The four marks used in this calculation come from the original 125-member family.

## Two points meet all small members

In every admissible family $F$ of at least 125 members, there are two points meeting every member of size at most three. If $F$ contains a pair, that pair already meets every member of $F$. A singleton would contradict Yang's starred bound. It remains to consider the intersecting family $\mathcal T$ of its three-element members.

The *covering number* of $\mathcal T$ is the fewest points meeting all its triples. Any of its own triples meets them all. Suppose the covering number is three. Frankl, Ota and Tokushige give the maximum of ten edges for such a system, and their seven extremal configurations each use at most seven vertices. The preceding bound forces $\mathcal T$ to consist of exactly ten nonprogression triples. [Frankl, Ota and Tokushige, Appendix 4.2](https://www.renyi.hu/~pfrankl/j79.pdf#page=9)

Let $V$ be the union of these triples and choose a family member $A$ outside $\mathcal T$. Every triple meets both $V\cap A$ and $V\setminus A$, because its intersection with $A$ has one or two points. Both parts are therefore covers of size at least three. Since $|V|\le7$, the smaller part is a three-element cover. It contains no triple of $\mathcal T$, because every triple meets the other part. Adjoining this new triple would give eleven intersecting triples, still with covering number three. Adding an edge cannot decrease the covering number, and each edge of an intersecting system is a cover. This contradicts the ten-edge bound.

This gives two possible patterns. Either one point occurs in all but at most four triple members, or every triple member contains at least two of the same three points. To see this, take a cover $\{p,q\}$. From the triples containing only $p$ of these points, remove $p$ to form a collection of pairs. Removing $q$ from the triples containing only $q$ gives a second collection. Every pair from one collection meets every pair from the other. If a collection contains two disjoint pairs, the other has at most four possible pairs. If both have at least five, each is an intersecting collection of pairs and must be a star, since an intersecting triangle admits no fourth edge. Their centres coincide because a pair avoiding one star's centre can meet at most two of its edges. Calling the common centre $c$ gives the three points $p,q,c$.

For a fixed point $x$, form a graph on the other fifteen points with edge $uv$ whenever $\{x,u,v\}$ is a nonprogression triple member. Every member omitting $x$ is a vertex cover of this graph, since it must meet every one of these triples. For each member containing $x$, apart from the triples defining the graph, deleting $x$ gives an independent set. Containing both ends of an edge would make its intersection with the defining triple a nonprogression.

## Reproduction

Run the prerequisite verifiers listed in the [four-element proof](four-or-more.md#reproduction), then run the expanded candidate calculation.

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic four_or_more.cpp -o /tmp/erdos272-four
/tmp/erdos272-four rank.weights short-progressions
/tmp/erdos272-four fixed-triple
/tmp/erdos272-four rank.weights seven-mark-support
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic small_root_search.cpp -o /tmp/erdos272-roots
/tmp/erdos272-roots residual-triples
```

The first run reports 178 large marked cases and 248 seven-term cases excluded at 125 members. The second reports 252 nonprogression triple cases excluded at 116 members of size at least four. The third excludes all 248 designated seven-term cases at a residual threshold of 121. The last excludes all 92 pair and progression-triple roots at 116 residual members.
