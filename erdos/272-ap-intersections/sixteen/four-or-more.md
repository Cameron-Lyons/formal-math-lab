# Families whose members have at least four elements

Extending the five-element bound one step further, we rule out large families that avoid all sets of size at most three:

**Theorem.** Any admissible family of subsets of $[16]$ whose members all have at least four elements has **at most 123 members**. Here an admissible family consists of distinct subsets whose pairwise intersections are nonempty arithmetic progressions.

**Consequence.** Removing all sets of size at most three from a hypothetical 125-member family leaves at most 123 members. Therefore any admissible family of size 125 must contain **at least two sets of size at most three**.

## Proof setup and root case split

Suppose for contradiction that $F$ is an admissible family of **124** subsets of $[16]$, all of size at least four.

**Step 1: $F$ has empty total intersection.** If every member of $F$ contained some common point $x$, we could adjoin the singleton $\{x\}$ and all 15 pairs $\{x, y\}$ ($y \ne x$). None of these 16 sets belonged to $F$ (since all members of $F$ have size $\ge 4$), and every intersection involving a newly added set contains $x$ and has size one or two, hence is a nonempty progression. Yang's upper bound of 124 for any family with a common point would then force $|F| + 16 \le 124$, i.e., $|F| \le 108$, contradicting $|F| = 124$. Thus $\bigcap_{A \in F} A = \varnothing$.

**Step 2: Apply two prerequisite bounds.** Because $F$ has empty total intersection and $|F| = 124$:

- **Marked sets:** At least $124 - 121 = 3$ members of $F$ belong to the fixed list of 363 *marked* subsets from the rank certificate ([marked-set bound](rank-mark.md)).
- **Four-element sets:** At most 93 members of $F$ have five or more elements ([five-element bound](five-or-more.md)), so at least $124 - 93 = 31$ members of $F$ have **exactly four elements**.

[Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004) · [Marked-set bound](rank-mark.md) · [Five-element bound](five-or-more.md)

**Step 3: Fix root marked members.** Every marked subset contains a seven-term arithmetic progression, so every marked member has size at least 7. Let $m$ be the maximum cardinality of a marked member in $F$:

- **Large marked root ($m \ge 8$):** Fix a marked member of size $m$. Identifying sets with their reflections ($i \mapsto 17 - i$) gives **178** possible choices.
- **Seven-term roots ($m = 7$):** Every marked member is itself a seven-term progression. Fix any three distinct marked members of $F$. Among the 14 seven-term progressions in $[16]$, there are **128** pairwise-compatible triples up to reflection.

In either case, call the fixed member(s) the **roots**. Every remaining candidate member must intersect every root in a nonempty progression, and every marked candidate must have size at most $m$.

## Excluding four-element candidates

**The big idea.** Instead of trying to bound the whole candidate pool in one shot, the verifier iteratively chips away at the list of still-possible four-element members. Testing one four-element set $S$ at a time lets us restrict the private-triple budget to triples that *hit* $S$ (since every surviving member must intersect $S$, triples disjoint from $S$ only dilute the budget). Every discarded four-element set shrinks the candidate list for the next pass, until either fewer than 31 four-element candidates remain or the root pool itself drops below 124.

**How a single test works.** Maintain the current list of still-possible four-element candidates. For each four-element candidate $S$ on the list, temporarily fix $S$ as an additional member of $F$ alongside the roots, and compute an upper bound on $|F|$ as follows (the same calculation with $S$ absent also bounds the roots alone):

1. **Localized private-triple budget:** Start from the 504 nonprogression triples and their arithmetic-progression hulls $H(T)$, exactly as in the [five-element bound](five-or-more.md).
   - *Price* only those nonprogression triples $T$ that intersect $S$ (or all 504 triples when $S$ is absent).
   - *Delete* from the budget every priced triple $T$ that is contained in any fixed member (any root, or $S$). Indeed, if such a triple $T$ were private to an unfixed member $A$, then $A$'s intersection with that fixed member would be a progression containing $T$ and hence containing $H(T)$, contradicting privacy.
   - Write $B$ for the number of remaining available priced triples.
2. **Augmented costs:** Each available priced triple $T$ counts toward the cost of its private owners, and we also assign $T$ to one eligible candidate progression containing $H(T)$—choosing the eligible progression of least current cost, just as in the five-element bound. At most one member of $F$ can claim $T$, so the sum of augmented costs over all unfixed members of $F$ is at most $B$.
3. **Incompatible color classes and multi-threshold bound:** Partition all unfixed candidates of augmented cost below 5 into classes of mutually incompatible sets. Process them in order of increasing cost and then increasing bit mask, inserting each candidate into the first class in which it is incompatible with every existing member (starting a new class if none qualifies). Let $c_i$ be the minimum cost in class $i$. For every integer threshold $d \in \{1, 2, 3, 4, 5\}$, each unfixed member $A \in F$ satisfies $d \le c(A) + \max(0, d - c(A))$, and at most one unfixed member belongs to each class $i$. Summing over unfixed members gives
   $$
   d \cdot |F_{\text{unfixed}}| \le B + \sum_i \max(0, d - c_i),
   $$
   so the number of unfixed members is at most
   $$
   \left\lfloor \frac{B + \sum_i \max(0, d - c_i)}{d} \right\rfloor .
   $$
4. **Elimination and iteration:** Add the number of fixed members to the minimum of this bound over $d \in \{1, 2, 3, 4, 5\}$ to bound $|F|$. If the resulting bound is below 124, no 124-member family can use $S$ alongside the roots and current candidates, so permanently discard $S$. Repeat passes over the four-element list until either a full pass discards nothing or the case closes. A case closes as soon as the root-only bound drops below 124 or fewer than 31 four-element candidates survive.

**Branching on additional marks.** Suppose a case with a single fixed largest marked member ($m \ge 8$) reaches a fixed point without closing. Because every remaining valid family must contain at least three marked members, it has a *least* unfixed marked member in bit-mask order. Branch over all remaining compatible marked candidates: fix the chosen candidate as an additional root, and exclude all smaller marked candidates (other than already-fixed roots) so each choice of extra marks is explored at most once. Re-run the elimination procedure and repeat if a third mark is still needed.

Checking every compatible branch settles all **178** large-marked cases and all **128** seven-term cases, proving no 124-member family exists.

## Reproduction

Run the two prerequisite verifiers and then the [four-element verifier](four_or_more.cpp) from this directory. All three programs use exact integer arithmetic.

```sh
c++ -O2 -std=c++20 -Wall -Wextra -Werror -pedantic rank_mark.cpp -o /tmp/erdos272-mark
/tmp/erdos272-mark rank.weights
c++ -O2 -std=c++20 -Wall -Wextra -Werror -pedantic five_or_more.cpp -o /tmp/erdos272-five
/tmp/erdos272-five
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic four_or_more.cpp -o /tmp/erdos272-four
/tmp/erdos272-four rank.weights
```

The final line of output is `178 large marked cases and 128 seven-term cases excluded at 124 members.`
