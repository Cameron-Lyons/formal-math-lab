# The exact maximum for intersections of at most six terms

**Theorem.** A family of distinct subsets of $\{1,\ldots,16\}$ whose pairwise intersections are arithmetic progressions of one through six terms has at most **124** members. This bound is attained.

## A family of 124

Start with all $1+15+\binom{15}{2}=121$ sets of size at most three containing 8. For each $d=1,2,3$, take the five-term progression $P_d$ with centre 8 and step $d$. Remove its two triples through 8 with unequal gaps. Add $P_d$ and its two four-term ends. Each replacement gains one set.

Two original sets meet in one or two points. An original set can meet an added set in a triple only if that triple survived the removal. Sets added at the same step meet in consecutive terms of $P_d$. At different steps their intersection contains 8 and lies in either $\{8\}$ or $\{6,8,10\}$. Thus every intersection is a progression of at most four terms. [Szabó’s construction, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) · [Lean verification](Erdos272Sixteen.lean)

## Why 125 is impossible

Any larger family would contain 125 members. Fix such a subfamily. It has no common point, since a family through one point has size at most 124. Call a progression of one through six terms *short*. [Yang’s starred bound, Theorem 1.4](https://arxiv.org/abs/2607.23004) · [Finite star check](general-bound.md#finite-check-for-sixteen-points)

**At least four members come from a list of 101.** Give each set $A$ a vector $u_A$ recording the constant 1 and its 120 pair-containment indicators. Let $v_A$ record containment of singletons and progressions of lengths three, four and six. If $a_j(S)$ counts $j$-term progressions in $S$, then
$$
u_A\cdot u_B-v_A\cdot v_B=q(A\cap B),\qquad
q(S)=1+\binom{|S|}{2}-|S|-a_3(S)-a_4(S)-a_6(S).
$$
The score is zero on every short progression. Mark every other nonempty set with $q(A)\le0$. Counting gives 101 marks.

A relation $\sum c_Au_A=0$ among unmarked members would give
$$
0=\Big\|\sum c_Av_A\Big\|^2+\sum c_A^2q(A),
$$
since distinct members have short intersections. Both terms are nonnegative, so the relation is supported on short progressions and also annihilates $v$. The short-progression lemma below rules this out. The unmarked vectors are therefore independent in dimension 121, leaving at least four marked members.

**No quartet can be the first four marks in a family of 125.** Fix an order on the marks. Choose the earliest quartet occurring in the family or its reflection $i\mapsto17-i$. Its reflection cannot come earlier, and every additional mark in the chosen family follows its fourth mark. There are 12,245 compatible quartets, including 13 fixed by reflection, so $(12{,}245+13)/2=6{,}129$ remain.

The same counting rule excludes all 6,129. A triple $a<b<c$ spans a progression $H$ from $a$ to $c$ with step $\gcd(b-a,c-b)$. Every progression containing the triple contains $H$. If one member contains the triple but misses part of $H$, no second member can contain that triple. The verifier counts these *private triples*. It groups candidates with few such triples into classes of mutually incompatible sets, since a family uses at most one set from each class. Applying the bound to candidates of size at least five tells it how many small sets are needed. It then tests small sets as fixed members and discards those that make 125 impossible. It also checks the candidates left after any such exclusions. This is the computer-assisted step. [Counting inequality](four-or-more.md#excluding-four-element-candidates) · [Integer implementation](private_triples.hpp) · [Quartet search](small_root_search.cpp)

## The short-progression lemma and replay

The two-element members share a point or lie in a triangle. Indeed, the only pair avoiding $x$ that meets both $\{x,y\}$ and $\{x,z\}$ is $\{y,z\}$. A singleton would force a common point. For each of the 16 stars and 560 triangles, allow its pairs and every progression of lengths three through six. Gaussian elimination modulo two finds just 16 distinct nonzero relations on the combined rows $(u_A,v_A)$. Each uses some five-term progression $P=\{a,b,x,c,e\}$ in increasing order, both pairs $\{a,x\},\{x,e\}$, and the middle triple $\{b,x,c\}$.

A member missing $x$ would have to contain both endpoints to meet those pairs. Its intersection with $P$ could then only be $\{a,e\}$, so it would miss the middle triple. Thus each relation forces a common point. This excludes real dependence too, since dependent integer rows admit an integer relation with an odd coefficient. [Finite rank check](verify_short.py) · [Proof of the lemma by hand](rank-mark.md#relations-among-short-progressions)

These commands check the starred bound, the 16 relations and all 6,129 quartets. Run them from this directory with Python 3.10 or later and a C++20 compiler.

```sh
c++ -std=c++20 -O3 small_root_search.cpp -o /tmp/erdos272-roots
python3 verify_short.py --replay /tmp/erdos272-roots
```

To check the construction in Lean, run `lake build` and `lake env leanchecker --fresh Erdos272Sixteen`.
