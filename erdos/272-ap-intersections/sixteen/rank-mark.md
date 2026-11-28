# A 363-mask condition for a family with no common point

How do we show that any hypothetical 125-member AP-intersecting family on $[16]$ must contain several "special" large sets? Using a signed-rank argument with a weighted diagonal-dominance certificate, we isolate a fixed list of **363 marked subsets** such that all other members of the family are linearly independent in dimension 121.

**Theorem.** Let $F$ be an admissible family of distinct subsets of $[16]$ with empty total intersection ($\bigcap_{A \in F} A = \varnothing$). There is a fixed, reflection-invariant list of **363 marked subsets** of $[16]$ such that at most **121** members of $F$ lie outside this list. Consequently, any 125-member family with empty total intersection must contain at least $125 - 121 = 4$ marked subsets (and more generally, a family of size $f$ contains at least $f - 121$ marked subsets).

In the verifier and [weight file](rank.weights), each subset $A \subseteq [16]$ is represented by a 16-bit integer mask with bit $0$ representing element $1$ (so bit $i$ represents $i + 1$). A weight of $0$ in `rank.weights` marks a mask; any mask omitted from the file receives the default weight $128$. All positive weights are integers.

## The big idea: signed rank plus diagonal dominance

Normally, working in dimension $1 + \binom{16}{2} = 121$ (the constant coordinate plus the 120 pair indicators) only gives a zero off-diagonal score on *short* intersections (progressions of lengths 1 through 6). When two large sets intersect in a progression of length 7 or more, the truncated score $q(A \cap B)$ becomes **negative**—for example, on a seven-term progression $P$, $q(P) = 1 + \binom{7}{2} - 7 - 9 - 5 - 2 = -1$.

At first glance, negative off-diagonal entries seem to spoil positive semidefiniteness of the Gram difference matrix $Q = (q(A \cap B))$. The key insight is **weighted diagonal dominance**: if a long set $A$ has a large enough positive diagonal score $q(A)$ to beat the worst-case sum of its negative off-diagonal interactions (after rescaling rows and columns by positive integer weights $w_A$), the long block of $Q$ stays **strictly positive definite**! We only have to put the 363 stubborn long sets that fail this diagonal-dominance margin onto the marked list.

## The rank argument

For each nonempty subset $A \subseteq [16]$, define two indicator vectors:

- $u_A \in \mathbb{R}^{121}$: the constant $1$ (containment of $\varnothing$) and the 120 pair-containment indicators $1_{\{x,y\} \subseteq A}$;
- $v_A$: the containment indicators for all singletons and all arithmetic progressions of lengths $3$, $4$, and $6$.

Writing $a_j(S)$ for the number of $j$-term arithmetic progressions contained in $S$, counting common coordinates gives
$$
u_A \cdot u_B - v_A \cdot v_B = q(A \cap B), \qquad
q(S) = 1 + \binom{|S|}{2} - |S| - a_3(S) - a_4(S) - a_6(S).
$$

Call a subset $A \subseteq [16]$ **short** if it contains no seven-term arithmetic progression, and **long** otherwise. The [verifier](rank_mark.cpp) checks finitely on $[16]$ that:

- $q(S) = 0$ on every short arithmetic progression (lengths 1 through 6);
- $q(S) > 0$ on every other nonempty short subset; and
- $q(S) \le 0$ on every nonempty arithmetic progression (of any length 1 through 16).

Now restrict the symmetric matrix $Q = \bigl(q(A \cap B)\bigr)$ to the **unmarked** members of $F$:

1. **Short unmarked members:** If $A$ is short, then for every other $B \in F$ the intersection $A \cap B$ is a short progression, so $q(A \cap B) = 0$. Every short member therefore sits in a diagonal block with $q(A) = 0$ on short progressions and $q(A) > 0$ on short nonprogressions.
2. **Long unmarked members:** For each long unmarked candidate $A$, gather all other possible long unmarked sets $B$ that are compatible with $A$ and have a negative off-diagonal score $q(A \cap B) < 0$. Partition these sets $B$ into classes $C$ of pairwise-incompatible subsets (where two sets are incompatible if their intersection is empty or fails to be a progression). Because $F$ is admissible, at most one member $B \in F$ can come from each class $C$.

Writing $w_A > 0$ for the assigned integer weight of each unmarked set, the verifier checks for every long unmarked candidate $A$ that
$$
q(A) w_A > \sum_C \max_{B \in C} \bigl(-q(A \cap B) w_B\bigr).
$$
Multiplying through by $w_A > 0$ shows that for the diagonal scaling matrix $D = \operatorname{diag}(w_A)$ on the long unmarked members of $F$, the symmetric matrix $M = D Q_{\text{long}} D$ is **strictly diagonally dominant**:
$$
M_{AA} = w_A^2 q(A) > \sum_{B \ne A} w_A w_B \bigl(-q(A \cap B)\bigr) = \sum_{B \ne A} |M_{AB}|.
$$
By the elementary inequality $2|xy| \le x^2 + y^2$, any strictly diagonally dominant symmetric matrix is positive definite:
$$
x^{\mathsf T} M x = \sum_A M_{AA} x_A^2 + \sum_{A < B} 2 M_{AB} x_A x_B \ge \sum_A \Bigl(M_{AA} - \sum_{B \ne A} |M_{AB}|\Bigr) x_A^2 > 0
$$
for all nonzero $x$. Hence $Q_{\text{long}}$ is positive definite. Combining the short and long blocks, the entire matrix $Q$ on unmarked members of $F$ is **positive semidefinite**, and $c^{\mathsf T} Q c = 0$ forces $c$ to be supported solely on short arithmetic progressions (lengths 1 through 6).

Now suppose the unmarked vectors $u_A$ satisfy a real linear relation $\sum c_A u_A = 0$. Taking the squared norm and substituting $u_A \cdot u_B = v_A \cdot v_B + q(A \cap B)$ gives
$$
0 = \left\|\sum c_A u_A\right\|^2 = \left\|\sum c_A v_A\right\|^2 + c^{\mathsf T} Q c.
$$
Since both terms are nonnegative, we must have $\sum c_A v_A = 0$ and $c^{\mathsf T} Q c = 0$, so $c$ is supported exclusively on progressions of lengths 1 through 6 and annihilates every coordinate of $(u, v)$. The next two sections show that any nonzero such relation forces every member of $F$ to share a common point, contradicting $\bigcap_{A \in F} A = \varnothing$. Therefore the unmarked vectors $u_A$ are linearly independent in $\mathbb{R}^{121}$, proving that at most 121 members of $F$ are unmarked.

## Relations among short progressions

Extend the coefficients $c_A$ by zero to all arithmetic progressions of lengths 1 through 6. Why could a nonzero relation on $(u_A, v_A)$ exist at all among short progressions? Because progressions of lengths $1, 2, 3, 4$, and $6$ all have their own containment coordinates in $(u, v)$, whereas **five-term progressions do not**. It turns out every relation comes from one explicit inclusion–exclusion identity per five-term progression.

Write $e_D$ for the standard basis vector at a set $D$ in coefficient space. Given a five-term progression $P = \{a, x - d, x, x + d, b\}$ with centre $x$, step $d$, endpoints $a = x - 2d$ and $b = x + 2d$, and outer triple $O = \{a, x, b\}$, define for any set $D \supseteq \{a, b\}$:
$$
h(D) = e_D - e_{D \setminus \{a\}} - e_{D \setminus \{b\}} + e_{D \setminus \{a,b\}},
\qquad
w_{x,d} = h(P) - h(O).
$$

*Concrete example ($x = 8, d = 1$):* Here $P = \{6, 7, 8, 9, 10\}$ and $O = \{6, 8, 10\}$, so
$$
w_{8,1} = \bigl(e_{\{6,7,8,9,10\}} - e_{\{7,8,9,10\}} - e_{\{6,7,8,9\}} + e_{\{7,8,9\}}\bigr)
        - \bigl(e_{\{6,8,10\}} - e_{\{8,10\}} - e_{\{6,8\}} + e_{\{8\}}\bigr).
$$
Notice the four terms with coefficient $+1$: the five-term progression $P$, its middle triple $\{7, 8, 9\}$, and the two pairs $\{6, 8\}$ and $\{8, 10\}$.

**Why $w_{x,d}$ annihilates $(u, v)$:** Evaluate $h(D)$ on the containment coordinate indexed by a set $T$ (summing coefficients of all $S$ with $T \subseteq S \subseteq D$). If $T \not\subseteq D$, the sum is $0$. If $T \subseteq D$ misses $a$, each term $S$ missing $a$ cancels with $S \cup \{a\}$; symmetrically if $T$ misses $b$. Only when $\{a, b\} \subseteq T \subseteq D$ does $S = D$ survive alone, giving $+1$. Thus:
$$
\text{value of } h(D) \text{ on coordinate } T = \begin{cases} 1 & \text{if } \{a, b\} \subseteq T \subseteq D, \\ 0 & \text{otherwise.} \end{cases}
$$
In particular, on the empty coordinate $T = \varnothing$, $h(D)$ evaluates to $0$. Now, which arithmetic progressions $T \subseteq P$ contain both endpoints $a$ and $b$? Any such progression has step $k d$ dividing $b - a = 4d$, so $k \in \{1, 2, 4\}$—meaning $T$ can only be $\{a, b\}$, $O = \{a, x, b\}$, or $P$ itself. Both $h(P)$ and $h(O)$ evaluate to $1$ on $\{a, b\}$ and $O$, so they cancel there; only $T = P$ distinguishes $h(P)$ from $h(O)$. Since $(u, v)$ has no five-term coordinate, $w_{x,d}$ annihilates every coordinate of $(u, v)$.

**Spanning all relations:** The only five-term progression appearing in $w_{x,d}$ is $P$ itself, with coefficient $+1$. Subtract $c_P w_{x,d}$ from $c$ for every five-term progression $P$. The remainder is still a relation on $(u, v)$, now supported purely on progressions of lengths $1, 2, 3, 4$, and $6$. Each of these progressions indexes its own containment coordinate in $(u, v)$: if the remainder were nonzero, an inclusion-maximal progression $M$ in its support would contribute a nonzero value at coordinate $M$ (since no larger support set contains $M$). Therefore the remainder is zero, and
$$
c = \sum_{x,d} \alpha_{x,d} w_{x,d}, \qquad \alpha_{x,d} = c_P.
$$

## Pairwise intersections force a common centre

We now show that any nonzero combination $c = \sum_{x,d} \alpha_{x,d} w_{x,d}$ supported on members of $F$ contradicts $\bigcap_{A \in F} A = \varnothing$. Set $\alpha_{x,d} = 0$ whenever the five-term progression with centre $x$ and step $d$ does not fit inside $[16]$, and call a centre $x$ *active* for step $d$ if $\alpha_{x,d} \ne 0$.

1. **Each active step has a unique active centre:** In $w_{x,d}$, the only pairs appearing are $\{x - 2d, x\}$ and $\{x, x + 2d\}$, both with span $2d$ and coefficient $+1$. No other step $d' \ne d$ produces a pair of span $2d$. Thus, for any fixed step $d$, the total coefficient of the pair $\{u, u + 2d\}$ in $c$ is exactly
   $$
   \alpha_{u,d} + \alpha_{u + 2d, d}.
   $$
   In any residue class modulo $2d$ that contains an active centre for step $d$, let $p$ be the smallest active centre and $q$ the largest. Then $\alpha_{p - 2d, d} = 0$ and $\alpha_{q + 2d, d} = 0$, so the pairs $\{p - 2d, p\}$ and $\{q, q + 2d\}$ have nonzero coefficients $\alpha_{p,d}$ and $\alpha_{q,d}$—forcing both pairs to belong to $F$!
   - If $p < q$, then $p \le q - 2d < q$, so $\{p - 2d, p\}$ and $\{q, q + 2d\}$ would be disjoint, contradicting admissibility of $F$.
   - Likewise, active centres in two different residue classes modulo $2d$ would force disjoint pairs into $F$.

   Hence each active step $d$ has **exactly one** active centre $x_d$, and both pairs $\{x_d - 2d, x_d\}$ and $\{x_d, x_d + 2d\}$ belong to $F$.

2. **All active steps share the same centre $x$:** If only one step is active, this is automatic. If two or more steps are active, their forced pairs have distinct spans $2d$, yielding at least **four** distinct pairwise-intersecting pairs in $F$. Any four pairwise-intersecting pairs must form a star (all containing one common point): indeed, given two pairs $\{x, y\}$ and $\{x, z\}$, the only pair missing $x$ that meets both is $\{y, z\}$, and no fourth distinct pair can meet all three edges of the triangle $\{x, y, z\}$. Because the two pairs forced by step $d$ meet only at $x_d$, all active steps must share the same common centre $x$.

3. **Contradiction at the smallest active step:** Let $d$ be the *smallest* active step at $x$, with five-term progression $P = \{x - 2d, x - d, x, x + d, x + 2d\}$ and middle triple $M = \{x - d, x, x + d\}$.
   - $P$ has coefficient $\alpha_{x,d} \ne 0$, so $P \in F$.
   - $M$ appears in $w_{x,d}$ with coefficient $+1$ (from $h(P)$). The only other vector $w_{x', d'}$ that could contain the triple $M$ is one whose *outer* triple $\{x' - 2d', x', x' + 2d'\}$ equals $M$—which requires $x' = x$ and $d' = d/2$. By minimality of $d$, step $d/2$ is either inactive or nonintegral. Thus $M$ has total coefficient $\alpha_{x,d} \ne 0$, so $M \in F$ as well.
   - Because $\bigcap_{A \in F} A = \varnothing$, choose a member $B \in F$ omitting $x$. To intersect both forced pairs $\{x - 2d, x\}$ and $\{x, x + 2d\}$, $B$ must contain both endpoints $x - 2d$ and $x + 2d$.
   - The intersection $B \cap P$ is an arithmetic progression inside $P$ containing both endpoints $x - 2d$ and $x + 2d$ while omitting $x$. The only progression inside $P$ with both endpoints and without $x$ is the pair $\{x - 2d, x + 2d\}$. Hence $B \cap P = \{x - 2d, x + 2d\}$, which implies $B \cap M = \varnothing$—contradicting the pairwise intersection condition!

Thus no nonzero relation exists, and the unmarked vectors $u_A$ are linearly independent in dimension 121. $\square$

## Reproduction

The [verifier](rank_mark.cpp) reconstructs all progressions and scores on $[16]$, verifies reflection symmetry and every weighted diagonal-dominance inequality from `rank.weights`, and prints the 363 marked masks in ascending order.

```sh
c++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic rank_mark.cpp -o /tmp/erdos272-mark
/tmp/erdos272-mark rank.weights
```

The first line of output is `remaining 363 pairs 23166`, where `23166` is the number of compatible unordered pairs among the 363 marked masks.
