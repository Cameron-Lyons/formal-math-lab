# Nonprogression triples are necessary

A *nonprogression triple* is a three-element set whose two successive gaps are unequal—for example, $\{1, 2, 4\}$ (gaps $1$ and $2$). If a nonprogression triple belongs to an admissible family $F$, it places a strong constraint on every other member $A \in F$: $A$ cannot avoid the triple (intersections must be nonempty) and cannot *contain* the triple (because the triple itself is not an arithmetic progression), so $A$ must intersect it in **one or two points**.

**Main Theorem.** Every admissible family $F$ of $k \ge 125$ subsets of $[16]$ contains **at least $k - 115$ nonprogression triples**. In particular, a 125-member family must contain at least **10** nonprogression triples. Furthermore, some pair of points in $[16]$ intersects every member of $F$ of size at most three.

The proof proceeds in three stages: first show that *at least one* nonprogression triple must appear; next use a single nonprogression triple to cap the number of sets of size $\ge 4$ at 115; finally rule out having 116 members free of nonprogression triples.

## Finding the first nonprogression triple

**Claim 1.** Any admissible family on $[16]$ containing no nonprogression triple has at most **124** members.

**Proof.** Suppose to the contrary that an admissible family $F$ of 125 members contains no nonprogression triple.

- Yang's starred bound rules out a common point, and therefore rules out any singleton member. Thus every member of $F$ is either a pair, one of the 56 three-term progressions, or a set of size at least four.
- At most 93 members have size at least five ([five-element bound](five-or-more.md)), forcing at least $125 - 93 = 32$ members of size at most four.
- The rank certificate forces at least $125 - 121 = 4$ marked members ([marked-set bound](rank-mark.md)).

[Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004) · [Five-element bound](five-or-more.md) · [Marked-set bound](rank-mark.md)

We now apply the [small-member elimination argument](four-or-more.md) to this expanded candidate list (pairs, three-term progressions, and sets of size $\ge 4$). Split into cases by the maximum size $m$ of a marked member in $F$:

- If $m \ge 8$, fix a largest marked member (**178** cases up to reflection).
- If $m = 7$, all four required marked members are distinct seven-term progressions (**248** pairwise-compatible quartets up to reflection).

In each case, successively test every remaining pair, three-term progression, and four-element set as a temporarily fixed member. The localized private-triple budget and incompatible color classes bound the family size; whenever the bound drops below 125, permanently discard that candidate. A case closes as soon as the root-only bound drops below 125 or fewer than 32 small candidates remain. If a large-marked case needs additional marked roots to close, the verifier branches just as in the four-element proof. All $178 + 248$ cases close.

## Sizes of the remaining members

**Claim 2.** If an admissible family $F$ contains at least one nonprogression triple $T$, then $F$ has **at most 115 members of size at least four**.

**Proof.** Fix a nonprogression triple $T$. Because no nonprogression triple is fixed by reflection $i \mapsto 17 - i$ (a symmetric triple would have midpoint $8.5$, which is nonintegral), the 504 nonprogression triples split into **252** reflection classes.

Suppose the subfamily of sets of size at least four had size 116. Since at most 93 members have size at least five, at least $116 - 93 = 23$ must have size exactly four. Every candidate meets $T$ in one or two points (none can contain $T$). Run the [four-element elimination procedure](four-or-more.md#excluding-four-element-candidates) with three adjustments:

- Price only private triples that meet $T$, and delete $T$ itself from the triple budget.
- When temporarily fixing a four-element candidate $S$, price only triples meeting *both* $T$ and $S$.
- Do not count the external triple $T$ toward the threshold of 116.

All 252 choices of $T$ close. Notably, this calculation uses only the five-element bound and requires **no rank certificate**.

Combining Claims 1 and 2 already shows that any family of size $k \ge 125$ contains at least $k - 115$ members of size at most three (at least 10 at $k = 125$).

## Counting nonprogression triples

We now upgrade "size at most three" to "nonprogression triples."

**Claim 3.** Let $F$ have $k \ge 125$ members, and let $R$ be obtained from $F$ by deleting all nonprogression triples. Then $|R| \le 115$, so $F$ contains at least $k - 115$ nonprogression triples.

**Proof.** By Claim 1, $F$ contains at least one nonprogression triple, so by Claim 2 at most 115 members of $F$ have size at least four. By Yang's bound, $F$ contains no singletons.

Suppose for contradiction that $|R| \ge 116$. Since at most 115 members of $R$ have size $\ge 4$, $R$ must contain at least one **pair or three-term progression** $S$. Fix $S$ and pass to a 116-member subfamily of $R$ containing $S$. Up to reflection, there are **64** choices for a pair ($\frac{120 + 8}{2} = 64$) and **28** choices for a three-term progression ($\frac{56}{2} = 28$), giving **92** cases in total.

For each choice of $S$, the [small-member search verifier](small_root_search.cpp) admits every other pair, three-term progression, and set of size $\ge 4$ meeting $S$ in a nonempty progression:

- The five-element bound ($\le 93$) forces at least $116 - 93 = 23$ members of size at most four (including $S$).
- Applying the [private-triple bound](four-or-more.md#excluding-four-element-candidates) separately to the whole candidate pool and to the size-$\ge 5$ pool can lower the large-set bound below 93, further increasing the required number of small sets.
- The verifier then iteratively discards any small candidate whose temporary inclusion either violates the private-triple bound or leaves too few mutually compatible small candidates (tested by partitioning small candidates into incompatible color classes, each contributing at most one member).

All 92 cases close. This final computation uses **no marked-member or long-intersection restrictions**. Thus $|R| \le 115$, and $|F \setminus R| \ge k - 115$.

## When the largest marked members have seven elements

An independent check gives a direct lower bound when no large marked set is present: if a 125-member family has no marked member of size eight or larger, it has **at least five nonprogression triples**. Indeed, deleting all nonprogression triples leaves all four required marked members intact (each is a seven-term progression). Across all 248 reflection classes of compatible seven-term quartets, the same small-member elimination bounds the nonprogression-triple-free residual subfamily by **120**, leaving at least $125 - 120 = 5$ nonprogression triples. (The four marks in this calculation come from the original 125-member family.)

## Two points meet all small members

Having at least 10 nonprogression triples tightly constrains how the small sets of $F$ can intersect.

**Proposition.** In every admissible family $F$ of at least 125 members, there exist two points in $[16]$ that together meet every member of size at most three.

**Proof.** Singletons are ruled out by Yang's starred bound. If $F$ contains any pair, that pair already meets every member of $F$ and we are done. Otherwise, every member of size at most three is a triple, forming a 3-uniform intersecting hypergraph $\mathcal{T}$ with $|\mathcal{T}| \ge 10$.

The *covering number* $\tau(\mathcal{T})$ is the minimum number of points needed to intersect every triple in $\mathcal{T}$. Because $\mathcal{T}$ is intersecting, any single triple $T \in \mathcal{T}$ is itself a cover, so $\tau(\mathcal{T}) \le 3$.

Suppose for contradiction that $\tau(\mathcal{T}) = 3$. A theorem of Frankl, Ota, and Tokushige shows that any intersecting 3-uniform hypergraph with covering number 3 has **at most 10 edges**, and all seven extremal 10-edge configurations live on **at most 7 vertices** ([Frankl, Ota and Tokushige, Appendix 4.2](https://www.renyi.hu/~pfrankl/j79.pdf#page=9)). Since $F$ has at least 10 nonprogression triples, $\mathcal{T}$ must consist of *exactly* 10 nonprogression triples!

Let $V = \bigcup_{T \in \mathcal{T}} T$ be the vertex set of $\mathcal{T}$ ($|V| \le 7$), and pick any member $A \in F \setminus \mathcal{T}$. For every triple $T \in \mathcal{T}$, $|A \cap T| \in \{1, 2\}$, so $T$ intersects *both* $V \cap A$ and $V \setminus A$. Consequently, both $V \cap A$ and $V \setminus A$ are covers of $\mathcal{T}$, so each has size at least $\tau(\mathcal{T}) = 3$. Since $|V \cap A| + |V \setminus A| = |V| \le 7$, the smaller of the two parts has size **exactly 3**; call this 3-element cover $E$.

- $E$ does not belong to $\mathcal{T}$, because every triple of $\mathcal{T}$ meets the complementary part $V \setminus E$, whereas $E$ is disjoint from $V \setminus E$.
- Because $E$ is a cover of $\mathcal{T}$, $\mathcal{T} \cup \{E\}$ is an intersecting 3-uniform hypergraph with **11 edges**.
- Adding an edge cannot reduce the covering number, and $E$ itself is a cover of size 3, so $\tau(\mathcal{T} \cup \{E\}) = 3$.

This contradicts the 10-edge maximum. Hence $\tau(\mathcal{T}) \le 2$, so some pair $\{p, q\}$ meets every member of size at most three. $\square$

### Two forced patterns and the link graph

Knowing a 2-point cover $\{p, q\}$ of $\mathcal{T}$ yields two further structural descriptions:

1. **Star-like or triangle-like triples:** Either *one point occurs in all but at most four triple members*, or *every triple member contains at least two of the same three points*.
   *Why?* Remove $p$ from the triples containing $p$ but not $q$ to get a collection of pairs $\mathcal{A}$, and remove $q$ from the triples containing $q$ but not $p$ to get a collection of pairs $\mathcal{B}$. Because $\mathcal{T}$ is intersecting, every pair in $\mathcal{A}$ must intersect every pair in $\mathcal{B}$.
   - If $\mathcal{A}$ contains two disjoint pairs, every pair in $\mathcal{B}$ must pick one point from each, giving $|\mathcal{B}| \le 2 \times 2 = 4$ (so $p$ lies in all but at most 4 triples). Symmetrically if $\mathcal{B}$ contains two disjoint pairs.
   - Otherwise, if both $|\mathcal{A}| \ge 5$ and $|\mathcal{B}| \ge 5$, each is an intersecting collection of pairs of size at least 5. Since a triangle has only 3 edges (and no fourth pair meets all three edges), both $\mathcal{A}$ and $\mathcal{B}$ must be stars. Their centres must coincide: an edge of one star avoiding the other star's centre can meet at most two edges of the second star. Calling this common centre $c$ gives three points $\{p, q, c\}$ such that every triple in $\mathcal{T}$ contains at least two of them.
2. **Vertex covers and independent sets around a point $x$:** Fix any point $x \in [16]$ and build the *link graph* $G_x$ on $[16] \setminus \{x\}$ whose edges are pairs $uv$ such that $\{x, u, v\} \in F$ is a nonprogression triple.
   - Every member $A \in F$ omitting $x$ must intersect every $\{x, u, v\}$, so $A$ is a **vertex cover** of $G_x$.
   - Every member $A \in F$ containing $x$ (other than those triples $\{x, u, v\}$ themselves) cannot contain both endpoints of any edge $uv \in G_x$—otherwise $A \cap \{x, u, v\} = \{x, u, v\}$, a nonprogression! Thus $A \setminus \{x\}$ is an **independent set** of $G_x$.

## Reproduction

Run the prerequisite verifiers listed in the [four-element proof](four-or-more.md#reproduction), then run the four checks below from this directory:

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic four_or_more.cpp -o /tmp/erdos272-four
/tmp/erdos272-four rank.weights short-progressions
/tmp/erdos272-four fixed-triple
/tmp/erdos272-four rank.weights seven-mark-support
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic small_root_search.cpp -o /tmp/erdos272-roots
/tmp/erdos272-roots residual-triples
```

Expected summaries of the four runs:

1. `short-progressions`: **178** large marked cases and **248** seven-term cases excluded at 125 members.
2. `fixed-triple`: **252** nonprogression triple cases excluded at 116 members of size at least four.
3. `seven-mark-support`: all **248** designated seven-term cases excluded at a residual threshold of 121.
4. `residual-triples`: all **92** pair and progression-triple roots excluded at 116 residual members.
