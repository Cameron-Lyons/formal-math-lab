# Families whose members have at least five elements

How large can an AP-intersecting family on $[16]$ be if we forbid all small sets (of size at most four)? Not very large at all:

**Theorem.** Any admissible family of subsets of $[16]$ whose members all have at least five elements has **at most 93 members**. Here "admissible" means that the intersection of every two distinct members is a nonempty arithmetic progression.

**Consequence.** Removing all sets of size at most four from a hypothetical 125-member family leaves an admissible family of sets of size at least five, which can contain at most 93 members. Therefore any 125-member family must include **at least $125 - 93 = 32$ sets of size at most four**.

## The big idea: private nonprogression triples

There are $\binom{16}{3} = 560$ triples in $[16]$. Exactly 56 of them are three-term arithmetic progressions, leaving **504 nonprogression triples**—triples $T = \{x, y, z\}$ ($x < y < z$) whose two successive gaps $y - x$ and $z - y$ are unequal.

Every triple $T = \{x, y, z\}$ forces a minimal progression around it. Define the **arithmetic-progression hull** $H(T)$ to be the progression running from $x$ to $z$ with common difference $\gcd(y - x, z - y)$.

- *Example:* For $T = \{1, 2, 4\}$, the gaps are $1$ and $2$ with $\gcd(1, 2) = 1$, so $H(T) = \{1, 2, 3, 4\}$. For $T = \{2, 4, 8\}$, the gaps are $2$ and $4$ with $\gcd(2, 4) = 2$, so $H(T) = \{2, 4, 6, 8\}$.

Any arithmetic progression containing $T$ must have step dividing both $y - x$ and $z - y$, hence dividing $\gcd(y - x, z - y)$, and must cover $[x, z]$; therefore every progression containing $T$ contains $H(T)$.

Now suppose a member $A$ of our family $F$ contains a nonprogression triple $T$ **without** containing its full hull ($H(T) \not\subseteq A$). Call $T$ a **private triple** of $A$. Why "private"? Because if any second distinct member $D \in F$ also contained $T$, then the intersection $A \cap D$ would be an arithmetic progression containing $T$, hence would contain $H(T)$—contradicting $H(T) \not\subseteq A$!

Define the initial **cost** $c(A)$ of a set $A$ to be the number of private nonprogression triples of $A$:
$$
c(A) = \#\{\text{nonprogression triples } T \subseteq A : H(T) \not\subseteq A\}.
$$
Because each of the 504 nonprogression triples can be private to at most one member of $F$, we immediately get a budget inequality: $\sum_{A \in F} c(A) \le 504$. Sets of size $\ge 5$ that are far from being progressions have huge costs, so they quickly eat up the budget.

## Refining the budget and handling progressions

Two refinements sharpen the raw budget of 504 down to the bound of 93:

1. **Case split on a longest progression member $P$:**
   Either $F$ contains a longest progression member $P$ (of size at least 5), or $F$ contains no progression member at all. Up to reflection ($i \mapsto 17 - i$), there are 55 choices for $P$, plus 1 case with no progression member, giving **56 cases** in total.
   - Whenever $P$ is fixed, no nonprogression triple $T \subseteq P$ can be private to *any* member $D \in F$ (for $D \ne P$, $D \cap P$ would be a progression containing $T$ and thus $H(T) \subseteq D$; and $P$ itself is a progression so $H(T) \subseteq P$). Removing all triples contained in $P$ from the 504 triples leaves a reduced budget $B$.
   - Every candidate member must also meet $P$ in a nonempty progression (including $P$ itself), and any candidate that is itself a progression can have size at most $|P|$.

2. **Charging progressions via augmented costs:**
   Left alone, a candidate progression $A$ has cost $c(A) = 0$ because it contains the hull of every triple inside it. To avoid letting many zero-cost progressions slip through for free, we assign each available triple $T$ **one extra possible owner**: a single candidate progression $A$ that contains $H(T)$.
   - *Why does this preserve the budget $\sum_{A \in F} c(A) \le B$?* Because $F$ can never contain *both* a private owner $D$ of $T$ and a progression $A \supseteq H(T)$: if both belonged to $F$, their intersection $D \cap A$ would be a progression containing $T$ and hence $H(T)$, contradicting $H(T) \not\subseteq D$. Since at most one progression is assigned each $T$, at most one member of $F$ claims $T$.
   - *Assignment rule:* Process the $B$ available triples in order of decreasing hull size $|H(T)|$, breaking ties by increasing bit mask (where bit $i$ represents the element $i + 1$). Assign $T$ to the eligible candidate progression containing $H(T)$ that currently has the lowest augmented cost, breaking ties by increasing bit mask. If no eligible progression contains $H(T)$, skip the assignment.

## Turning costs into a size bound

Now compare every candidate's augmented cost $c(A)$ against a target threshold of $8$:

- Any member with $c(A) \ge 8$ already contributes at least $8$ to the budget sum.
- Any candidate with $c(A) < 8$ has a positive shortfall (weight) $8 - c(A)$.

To bound the total shortfall across $F$, sort all candidates with $c(A) < 8$ by increasing augmented cost $c(A)$, breaking ties by increasing bit mask (bit $i$ representing $i + 1$). Greedily partition these low-cost candidates into **incompatible color classes**: insert each candidate into the first class in which its intersection with every existing member is empty or fails to be a progression, starting a new class if none qualifies.

Because any two members of $F$ must intersect in a nonempty progression, $F$ can select **at most one candidate from each class**. Since candidates were processed in increasing order of cost (hence decreasing order of weight $8 - c(A)$), the very first candidate placed into class $i$ achieves the maximum weight $w_i$ in that class. Therefore, for every admissible family $F$ in the case,
$$
8|F| \le \sum_{A \in F} c(A) + \sum_{A \in F} \max(0, 8 - c(A))
     \le B + \sum_i w_i,
$$
so $|F| \le \left\lfloor \bigl(B + \sum_i w_i\bigr) / 8 \right\rfloor$.

## Verification and reproduction

The [C++ verifier](five_or_more.cpp) evaluates this integer upper bound across all 56 cases. The maximum bound attained over all cases is **93**. To reproduce it, run the following commands in this directory:

```sh
c++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic five_or_more.cpp -o /tmp/erdos272-five-or-more
/tmp/erdos272-five-or-more
```
