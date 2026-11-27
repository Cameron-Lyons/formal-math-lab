# Families whose members have at least five elements

An admissible family of subsets of $[16]$ whose members all have at least five elements has **at most 93 members**. Here “admissible” means that the intersection of every two distinct members is a nonempty arithmetic progression. Thus a family of 125 would contain at least 32 sets of size at most four. Removing all its smaller members leaves an admissible family to which the bound applies.

For a triple $T=\{x,y,z\}$ with $x<y<z$, its arithmetic-progression hull $H(T)$ runs from $x$ to $z$ with step $\gcd(y-x,z-y)$. Every progression containing $T$ contains $H(T)$. Define the cost $c(A)$ of a set $A$ as the number of nonprogression triples $T\subseteq A$ for which $H(T)\not\subseteq A$. If such a triple occurred in a second family member $D$, the progression $A\cap D$ would contain $H(T)$. Each of the 504 nonprogression triples can therefore contribute to the cost of at most one member.

Choose a longest progression $P$ among the members of the family. There is also a case with no progression member. Triples contained in $P$ cannot contribute to any cost. Write $B$ for the number of the 504 triples left available. When $P$ exists, every member meets it in a nonempty progression, including $P$ itself, and every progression member has size at most $|P|$. Reflection of $[16]$ leaves 55 possible choices for $P$, plus the case with no $P$.

For each available triple $T$, allow one more possible owner, a candidate progression $A$ containing $H(T)$. If a private owner $D$ occurred with $A$, the progression $D\cap A$ would contain $T$ and hence $H(T)$, contrary to the definition of a private owner. Thus the sum of the augmented costs is still at most $B$. To choose the additional owners, process triples by decreasing hull size, breaking ties by increasing bit mask. Among the eligible progression owners of each triple, assign it to the one with lowest current cost, breaking ties by increasing mask. Skip the assignment when there is no such owner.

Give each candidate of augmented cost below eight a weight of $8-c(A)$. Sort these candidates by increasing cost, breaking ties by increasing bit mask, with bit $i$ representing $i+1$. Put each candidate into the first class in which its intersection with every existing member is empty or fails to be a progression. Start a new class whenever none qualifies. The family can use at most one candidate per class. The first candidate in each class has the largest weight $w_i$ in that class, by the ordering.

Each family satisfies

$$
8|F| \le \sum_{A\in F} c(A) + \sum_{A\in F}\max(0,8-c(A))
     \le B+\sum_i w_i.
$$

The [C++ verifier](five_or_more.cpp) computes the integer upper bound in all 56 cases. The largest bound is 93. To reproduce it, run these commands in this directory.

```sh
c++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic five_or_more.cpp -o /tmp/erdos272-five-or-more
/tmp/erdos272-five-or-more
```
