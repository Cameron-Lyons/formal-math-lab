# Why 83 sets are impossible

**Claim.** The largest family of subsets of $[13]$ whose pairwise intersections are nonempty arithmetic progressions has size **82**.

Szabó's construction attains 82. Write AP for arithmetic progression. For families with a common element $x$, Yang's starred-family theorem gives the bound 82; the verifier also checks it directly at $n = 13$ by assigning each non-AP of size $\ge 4$ to a non-AP triple $t$ containing $x$ whose AP-hull it omits, and matching all but at most 3 APs of size $\ge 4$ injectively to those triples (giving at most $1 + 12 + \binom{12}{2} + 3 = 82$ sets). It remains to rule out an 83-set family $F$ with **no common element** (and hence no singletons).

## 1. Set aside 300 subsets

Set aside the 300 subsets containing a seven-term AP, and let $F_0 \subseteq F$ be the remaining members. We show $|F_0| \le 79$.

For a set $A$, let $u_A$ record which of the empty set and the 78 pairs lie in $A$, and let $v_A$ record which singletons and which three-, four-, and six-term APs lie in $A$ (0/1 entries). Writing $a_j(S)$ for the count of $j$-term APs in $S$, put
$$
q(S) = 1 + \binom{|S|}{2} - |S| - a_3(S) - a_4(S) - a_6(S).
$$
Counting common coordinates gives $u_A \cdot u_B - v_A \cdot v_B = q(A \cap B)$. The verifier checks all 7,891 nonempty subsets avoiding a seven-term AP and finds $q(S) = 0$ on APs and $q(S) > 0$ on all other sets.

Suppose $\sum_{A \in F_0} c_A u_A = 0$. Squaring and using $q(A \cap B) = 0$ for $A \ne B$ yields
$$
0 = \left\|\sum_{A \in F_0} c_A v_A\right\|^2 + \sum_{A \in F_0} c_A^2 q(A).
$$
Hence $c_A = 0$ for every non-AP $A \in F_0$ and $\sum c_A v_A = 0$, so $c \in \ker(u, v)$ is supported on APs in $F_0$ of length $2, 3, 4, 5, 6$. For each of the 15 five-term APs $P = \{x - 2d, x - d, x, x + d, x + 2d\}$ with four-term ends $P_L, P_R$, a direct check shows
$$
w_P = e_P - e_{P_L} - e_{P_R} - e_{\{x - 2d, x, x + 2d\}} + e_{\{x - d, x, x + d\}} + e_{\{x - 2d, x\}} + e_{\{x, x + 2d\}} - e_{\{x\}}
$$
lies in $\ker(u, v)$. Subtracting $\sum_P c_P w_P$ from $c$ leaves a vector in $\ker(u, v)$ supported on APs of lengths $1, 2, 3, 4, 6$. Each such AP is itself a coordinate of $(u, v)$, so an inclusion-maximal nonzero AP gives a contradiction. Thus $c = \sum_P \alpha_P w_P$ with $\alpha_P = c_P$.

Since $F$ has no singletons, the singleton coefficient $-\sum_{P \text{ centred at } x} \alpha_P$ vanishes at every $x \in [13]$. Centers $3, 4, 10, 11$ admit only one five-term AP, so their weights vanish; any active center must lie in $\{5, 6, 7, 8, 9\}$. Checking which $w_P$ contain each pair shows that each active center $x \in \{5, 6, 7, 8, 9\}$ forces two pairs $\{u_1, x\}, \{u_2, x\} \in F$ with $u_1, u_2 \notin \{5, 6, 7, 8, 9\}$:

- $x = 5$: $\{1, 5\}, \{3, 5\}$
- $x = 6$: $\{2, 6\}, \{6, 10\}$
- $x = 7$: $\{3, 7\}, \{7, 11\}$ or $\{1, 7\}, \{7, 13\}$
- $x = 8$: $\{4, 8\}, \{8, 12\}$
- $x = 9$: $\{9, 11\}, \{9, 13\}$

No two active centers $x \ne y$ can coexist, because a forced pair $\{u, x\}$ avoids $y$ and cannot hit both distinct outer endpoints of $y$'s forced pairs. Thus at most one center $x$ is active. Let $d$ be the smallest step with $\alpha_{x, d} \ne 0$. Since no other center is active and $\alpha_{x, d/2} = 0$, the pairs $\{x - 2d, x\}$ and $\{x, x + 2d\}$, the five-term AP $P_{x, d}$, and its middle triple $M_{x, d} = \{x - d, x, x + d\}$ all have nonzero coefficient $\alpha_{x, d}$ and lie in $F$. Pick $B \in F$ omitting $x$. To intersect both pairs, $B$ contains $x - 2d$ and $x + 2d$. Since $B \cap P_{x, d}$ is an AP omitting $x$, $B$ omits $x - d$ and $x + d$, giving $B \cap M_{x, d} = \emptyset$, a contradiction. Thus $c = 0$, the vectors $u_A$ ($A \in F_0$) are independent, and $|F_0| \le 1 + \binom{13}{2} = 79$.

## 2. Check the families using four of the 300 subsets

An 83-set non-starred family therefore needs at least $83 - 79 = 4$ of the 300 subsets containing a seven-term AP. Join two subsets by an edge when their intersection is a nonempty AP; a valid family is a clique. Order the 300 subsets in consecutive reflection pairs $\{A, \overline{A}\}$ under $i \mapsto 14 - i$. Up to reflection, the first exceptional member satisfies $A \le \overline{A}$ (and if $A = \overline{A}$, so does the second), leaving 3,224 compatible choices for the first two. For each choice, an exhaustive branch-and-bound clique search looks for 81 common neighbors including two further exceptional sets and with empty total intersection, pruning whenever fewer than the needed independent sets cover the remaining candidates. None exists. Thus 83 is impossible, and 82 is the maximum. $\blacksquare$

---

**Reproduce all finite checks** with [clique_search/verify.cpp](clique_search/verify.cpp): compile with `c++ -O3 -std=c++23 -march=native clique_search/verify.cpp -o verify` and run `./verify`. Szabó's construction and Yang's starred theorem appear in [Yang, arXiv:2607.23004](https://arxiv.org/abs/2607.23004).
