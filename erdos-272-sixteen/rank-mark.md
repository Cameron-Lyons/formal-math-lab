# A 363-mask condition for a family with no common point

Let $F$ be a family of distinct subsets of $[16]$ whose pairwise intersections are nonempty arithmetic progressions, and suppose the intersection of all its members is empty. There is a fixed, reflection-invariant list of 363 masks such that at most 121 members of $F$ lie outside the list. A family of size 125 would therefore contain at least four listed masks.

Represent each subset by a bit mask, with bit zero denoting 1. In the [weight file](rank.weights), a zero weight marks a mask. An omitted mask has weight 128. All positive weights are integers.

## The rank argument

For each nonempty set $A$, let $u_A$ be its containment indicators for the empty set and the 120 pairs. Let $v_A$ be the containment indicators for singletons and progressions of lengths 3, 4, and 6. Write $a_j(S)$ for the number of $j$-term progressions contained in $S$. Then

$$
u_A\cdot u_B-v_A\cdot v_B=q(A\cap B),\qquad
q(S)=1+\binom{|S|}{2}-|S|-a_3(S)-a_4(S)-a_6(S).
$$

Call a set *short* if it contains no seven-term progression. The verifier checks that every short progression has score zero, every other nonempty short set has positive score, and every nonempty progression has nonpositive score.

Restrict the symmetric matrix $Q=(q(A\cap B))$ to unmarked members of $F$. A short member has zero off-diagonal entries because every other member meets it in a short progression. For a long unmarked member $A$, group all other possible long unmarked members $B$ with negative off-diagonal entry into classes whose members are pairwise incompatible. Here two sets are incompatible if their intersection is empty or fails to be a progression. Each class contributes at most one member to $F$.

Writing $w_A$ for the assigned weight, the verifier checks for every long unmarked $A$ that

$$
q(A)w_A > \sum_C\max_{B\in C}\bigl(-q(A\cap B)w_B\bigr).
$$

Thus, for $D=\operatorname{diag}(w_A)$ on long unmarked members of $F$, the symmetric matrix $D Q D$ has diagonal entries larger than the sums of the absolute off-diagonal entries. It is positive definite by the inequality $2|xy|\le x^2+y^2$. The full $Q$ on unmarked members is positive semidefinite, and its kernel is supported on short progressions.

If $\sum c_A u_A=0$ on the unmarked members, then

$$
0=\left\|\sum c_Av_A\right\|^2+c^{\mathsf T}Qc.
$$

Hence $\sum c_Av_A=0$ and the relation is supported on progressions of lengths one through six. The short-progression relation argument shows that any such nonzero relation forces every member of $F$ to contain a common point. That contradicts the hypothesis. Therefore the unmarked vectors $u_A$ are independent in dimension 121.

## Relations among short progressions

Extend the coefficients by zero to all progressions of lengths one through six.

Write $e_A$ for the unit coefficient at $A$. For a five-term progression $P$ with centre $x$ and step $d$, let $a=x-2d$, $b=x+2d$, and $O=\{a,x,b\}$. For any $D$ containing $a,b$, put

$$
h(D)=e_D-e_{D\setminus\{a\}}-e_{D\setminus\{b\}}+e_{D\setminus\{a,b\}},
\qquad w_{x,d}=h(P)-h(O).
$$

On the containment coordinate indexed by $T$, inclusion–exclusion evaluates $h(D)$ to 1 when $\{a,b\}\subseteq T\subseteq D$ and to 0 otherwise. A progression inside $P$ containing both endpoints is either $\{a,b\}$, $O$, or $P$ because its step in units of $d$ must divide 4. Only $P$ distinguishes $h(P)$ from $h(O)$ on a progression coordinate, and the vectors $(u,v)$ have no five-term coordinate. The empty coordinate also cancels. Hence each $w_{x,d}$ gives a relation among the concatenated vectors $(u_A,v_A)$.

The only five-term coefficient in $w_{x,d}$ is $+1$ at $P$. Subtract $c_Pw_{x,d}$ from $c$ for each five-term $P$. The result is a relation supported on progressions of lengths 1, 2, 3, 4, and 6. Each one is itself a coordinate of $(u,v)$. An inclusion-maximal set with nonzero coefficient would give a nonzero value at its own coordinate. Consequently

$$
c=\sum_{x,d}\alpha_{x,d}w_{x,d},\qquad \alpha_{x,d}=c_P.
$$

## Pairwise intersections force a common centre

Set $\alpha_{x,d}=0$ when the corresponding five-term progression does not lie in $[16]$. For a fixed step $d$ the coefficient of the pair $\{u,u+2d\}$ is $\alpha_{u,d}+\alpha_{u+2d,d}$, since the two pairs in $w_{x,d}$ are $\{x-2d,x\}$ and $\{x,x+2d\}$, both with sign $+1$. No other step contributes to a pair of that span.

In any residue class modulo $2d$ with nonzero coefficients $\alpha_{x,d}$, take the first and last such centres $p,q$. Then the pairs $\{p-2d,p\}$ and $\{q,q+2d\}$ have nonzero coefficients and must belong to $F$. They would be disjoint if $p<q$. Pairs arising from different residue classes would also be disjoint. Thus for each step with a nonzero coefficient there is exactly one active centre, and both pairs at that centre belong to $F$.

If two or more steps are active, they contribute at least four distinct pairwise intersecting pairs. To see that these pairs share a vertex, take two of them, $xy$ and $xz$. The only pair missing $x$ and meeting both is $yz$, and no fourth distinct pair meets all three edges of that triangle. At every active step the two pairs meet only at their centre. Hence all active steps have the same centre $x$. For a single active step this also holds.

Take the least active step $d$ at $x$. Its five-term progression $P$ has nonzero coefficient $\alpha_{x,d}$. Its middle triple $M=\{x-d,x,x+d\}$ occurs with sign $+1$ in $h(P)$. Its only other possible contribution comes from the outer triple of step $d/2$, which is inactive or nonintegral. Its coefficient is therefore $\alpha_{x,d}$. Thus $P,M\in F$. Choose $B\in F$ omitting $x$. To meet the two forced pairs, $B$ must contain both endpoints of $P$. The only progression in $P$ containing both endpoints and omitting $x$ is the pair of endpoints. Therefore $B\cap P=\{x-2d,x+2d\}$ and $B\cap M=\varnothing$, contradicting the pairwise intersection hypothesis.

## Reproduction

The [verifier](rank_mark.cpp) reconstructs the progressions and scores, checks all weight inequalities and reflection symmetry, and prints the marked masks in ascending order. The first output line is `remaining 363 pairs 23166`. The pair count is the number of compatible unordered pairs of marked masks.

```sh
c++ -std=c++20 -O2 -Wall -Wextra -Werror -pedantic rank_mark.cpp -o /tmp/erdos272-mark
/tmp/erdos272-mark rank.weights
```
