# Families whose members have at least four elements

An admissible family of subsets of $[16]$ whose members all have at least four elements has **at most 123 members**. Consequently, an admissible family of size 125 would contain at least two sets of size at most three. Here an admissible family has distinct members whose pairwise intersections are nonempty arithmetic progressions.

Suppose a family $F$ of exactly 124 members violated the bound. If all its members contained a point $x$, we could adjoin the singleton $\{x\}$ and all 15 pairs through $x$. Each new intersection would contain $x$ and have at most two elements. Yang's upper bound of 124 for a family with a common point therefore gives $|F|\le108$ in that case. Thus $F$ has empty total intersection. Two verified results then apply. At least three members belong to the fixed list of 363 marked sets, and at least 31 members have exactly four elements. The second assertion follows because at most 93 members have five or more elements. [Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004) · [Marked-set bound](rank-mark.md) · [Five-element bound](five-or-more.md)

Every marked member contains a seven-term progression. Choose a marked member of maximum cardinality $m$. If $m\ge8$, fix this member. Reflection gives 178 possible choices. If $m=7$, every marked member is itself a seven-term progression. Fix any three distinct such members of $F$. There are 128 pairwise-compatible choices up to reflection among the fourteen seven-term progressions. In either case call the fixed members the roots. Every remaining candidate must meet each root in a nonempty progression, and every marked candidate has size at most $m$.

## Excluding four-element candidates

The verifier maintains a list of four-element sets that could occur in the family. For each one, $S$, temporarily fix it as an additional member. The following bound either rules $S$ out or leaves it on the list. The verifier removes a set only after proving that no family of the required size can use it alongside the roots and the current candidates. The same calculation with the roots alone can sometimes exclude an entire case.

Use the 504 nonprogression triples and their progression hulls as in the five-element bound. Price only triples that meet $S$, or all triples when $S$ is absent. Remove from the budget every priced triple contained in any fixed member. If such a triple $T$ were private to a remaining member $A$, its intersection with the fixed member would be a progression containing $T$ and hence its hull, contradicting privacy. Each available triple can be assigned to its private owners and also to one candidate progression containing its hull. A family uses at most one of these possible owners. As in the five-element bound, the verifier assigns this additional owner to the eligible progression of least current cost.

Write $B$ for the number of available priced triples. The total cost of the unfixed family members is at most $B$. Partition candidates of cost below five into classes of mutually incompatible sets, processing them in increasing order of cost and then mask, and inserting each new set into the first class in which it is incompatible with every existing member. Start a new class if none qualifies. Write $c_i$ for the minimum cost in class $i$. For every integer $d$ from one to five, the number of unfixed members is at most

$$
\left\lfloor\frac{B+\sum_i\max(0,d-c_i)}{d}\right\rfloor .
$$

Indeed, each member contributes its cost plus its positive discount towards $d$, and at most one member belongs to each class. Add the fixed members to obtain the bound for the entire family. If the bound is below 124, discard $S$. Repeat until the case closes or a full pass removes nothing. A case closes when the bound with the roots alone is below 124 or fewer than 31 four-element candidates remain.

For a fixed largest marked member that this procedure does not exclude, choose the least remaining marked member in mask order. Every family still under consideration contains at least three marks. Fix the chosen member as an additional root and exclude all smaller marks except the already fixed roots. Repeat if necessary. The verifier checks every compatible choice of these additional members. This settles all 178 cases with a large marked member and all 128 cases with three seven-term roots.

## Reproduction

Run the two prerequisite verifiers and the four-element verifier in this directory. All three use integer arithmetic. [Four-element verifier](four_or_more.cpp)

```sh
c++ -O2 -std=c++20 -Wall -Wextra -Werror -pedantic rank_mark.cpp -o /tmp/erdos272-mark
/tmp/erdos272-mark rank.weights
c++ -O2 -std=c++20 -Wall -Wextra -Werror -pedantic five_or_more.cpp -o /tmp/erdos272-five
/tmp/erdos272-five
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic four_or_more.cpp -o /tmp/erdos272-four
/tmp/erdos272-four rank.weights
```

The final line is `178 large marked cases and 128 seven-term cases excluded at 124 members.`
