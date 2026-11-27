# Arithmetic-progression intersections on fifteen points

Let $t(15)$ be the maximum number of distinct subsets of $[15]=\{1,\ldots,15\}$
whose pairwise intersections are nonempty arithmetic progressions. Singletons
and pairs count as progressions. **The maximum is 109.** The lower bound is
Szabó's construction. The computer-assisted upper bound below reduces a
hypothetical family of 110 to 46,886 finite clique searches. It extends the
lab's thirteen-point argument and the fourteen-point search in commit
`b8f6e31`. [Thirteen-point proof](../erdos-272-thirteen/) ·
[Erdős problem #272](https://www.erdosproblems.com/272)

## A family of 109

Begin with the $1+14+\binom{14}{2}=106$ sets of size at most three containing
$x=8$. For each $d=1,2,3$, form the five-term progression
$P_d=\{x-2d,x-d,x,x+d,x+2d\}$. Remove the two triples
$\{x-2d,x,x+d\}$ and $\{x-d,x,x+2d\}$, and add $P_d$ and the two
four-term progressions obtained by deleting one endpoint. This gives
$106-6+9=109$ distinct sets.

All intersections contain 8. Two distinct original sets intersect in at most
two points. Two inserted progressions intersect in a progression, since each
is an interval in a residue class. A retained triple lying inside an inserted
progression is an arithmetic progression itself because the only two nonprogression
triples through 8 inside $P_d$ were removed. A retained triple meeting an
inserted progression in fewer than three points also gives a progression.
Lean's kernel checks distinctness and all 5,886 pairwise intersections.
[Lean construction](Erdos272Fifteen.lean) · [Szabó, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf)

## Why 110 would require four sets containing seven-term progressions

Yang's Theorem 1.4 bounds any family with a common point by
$1+\binom{15}{2}+\lfloor 14/4\rfloor=109$. It suffices to rule out an
admissible family $F$ of exactly 110, since every larger family contains one.
Such an $F$ has empty total intersection and contains no singleton.
[Yang, Theorem 1.4](https://arxiv.org/html/2607.23004v1#S1)

Let $F_0$ consist of the members of $F$ that contain no seven-term
progression. For a set $A$, let $u_A$ be the vector comprising a constant
1 and the containment indicators for the 105 unordered pairs. Let $v_A$
record containment of the singletons and the progressions of lengths 3, 4,
and 6. If $a_j(S)$ counts the $j$-term progressions in $S$, then

$$
u_A\cdot u_B-v_A\cdot v_B=q(A\cap B),\qquad
q(S)=1+\binom{|S|}{2}-|S|-a_3(S)-a_4(S)-a_6(S).
$$

This identity counts the coordinates shared by $A$ and $B$. On all 31,055
nonempty subsets of $[15]$ containing no seven-term progression, the C++
verifier checks that $q(S)=0$ for a progression and $q(S)>0$ otherwise.
In particular $q(A\cap B)=0$ for distinct $A,B\in F_0$.
[Score and search verifier](../erdos-272-thirteen/clique_search/verify.cpp)

Suppose $\sum_{A\in F_0}c_Au_A=0$ is a nonzero real relation. Squaring and
using the identity gives

$$
0=\left\|\sum_{A\in F_0}c_Av_A\right\|^2
   +\sum_{A\in F_0} c_A^2 q(A).
$$

Both terms are nonnegative. The relation therefore uses only progressions of
lengths 2 through 6 and also annihilates the $v$ coordinates. The concatenated
rows $(u_A,v_A)$ have integer entries. Row reduction over the rationals on the
same support yields a nonzero rational relation. Clear denominators and divide
out the common divisor of the coefficients. Reducing modulo 2 now gives a
nonzero binary relation supported within $F$.

The Python verifier builds all 220 possible progression rows on the 215
coordinates and enumerates the binary kernel by elimination. Of its 1,023
nonzero relations, only 13 have pairwise compatible supports. For each of the
13, it enumerates **every** subset of $[15]$ meeting every support member in
a nonempty progression. These subsets all share a point. This includes the
support members themselves, since they are progressions. The entire family
$F$ would consequently share that point, a contradiction. Thus the $u_A$ for
$A\in F_0$ are independent. They have 106 coordinates, so $|F_0|\le106$.
At least four members of $F$ must contain a seven-term progression.
[Finite rank verifier](rank.py)

## Exhausting the starting pairs

Join two distinct subsets of size at least two when their intersection is a
nonempty progression. A family as above is a clique in this graph. Call a
subset exceptional if it contains a seven-term progression. There are
1,712 exceptional subsets. Order them by degree, grouping each subset with
its reflection $i\mapsto16-i$ and putting the smaller bit mask first inside
each orbit. Reflecting a clique preserves every intersection condition. We
may therefore choose its first exceptional member to be the smaller mask in
its orbit. If this member is fixed by reflection, the same choice is available
for the second member. This gives 46,886 compatible starting pairs.

For each pair, form its common neighborhood and remove the exceptional
members earlier than or equal to the second. Keep every ordinary common
neighbor. A completion needs 108 more mutually adjacent vertices, including
at least two further exceptional vertices, and its total intersection with
the starting pair must be empty.

At a recursive node needing $k$ vertices, each independent set can supply at
most one. After removing $j$ independent sets the node can therefore be
discarded if fewer than $k-j$ candidates remain. Otherwise, after $k-1$
such sets, every completion must use an uncovered vertex. Other necessary
choices include an exceptional vertex while one is still required, and a
vertex omitting each point common to the selected sets. The verifier chooses
the smallest of these necessary pools. It tries every vertex in that pool,
retaining its neighbors and excluding only pool vertices already tried at
the node. This covers every possible completion.
[Exhaustive search](../erdos-272-thirteen/clique_search/verify.cpp)

The completed run checked all **46,886** starting pairs and visited
**148,574,329** recursive nodes. No starting pair extended to a family of
110. An audit of the 733 run intervals found every pair exactly once, and an
independent enumeration reproduced the common-neighbor counts for every pair
(166 to 8,198 candidates). Together with the construction, this proves
$t(15)=109$.

## Direct check for families with a common point

The C++ program also verifies the starred bound on $[15]$ without calling an
external solver. Fix a centre $x$. Give each of the 106 sets of size at most
three containing $x$ its own class. For each nonprogression triple $T$ through
$x$, let $H(T)$ be the intersection of all progressions containing $T$. A set
$A$ containing $T$ and missing part of $H(T)$ cannot have a progression as
its intersection with any other set containing $T$. The verifier checks that
every nonprogression $A$ of size at least four through $x$ has such a triple,
so it can go in that triple's class.

For each progression of size at least four through $x$, the verifier tries to
match it to a distinct nonprogression triple that it contains. A matched
progression fits in its triple's class by the same argument. For each centre
at most three progressions are left unmatched, and each gets its own class.
Thus at most $106+3=109$ classes suffice, with at most one family member per
class.

## Reproduce

Run from this directory with Lean 4.36.0, Python 3.10 or later, and a C++23
compiler.

```sh
lake --wfail build
lake env leanchecker --fresh Erdos272Fifteen
python3 rank.py
c++ -O3 -std=c++23 -march=native -DERDOS272_N=15 ../erdos-272-thirteen/clique_search/verify.cpp -o /tmp/erdos272-check15
/tmp/erdos272-check15
```

The last command checks every pair. To divide the work among processes, pass
two zero-based indices to check a half-open range. A complete run must cover
all of $[0,46886)$.
