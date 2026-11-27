# Families with no common point

Let $F$ be a family of at least two distinct subsets of $[N]=\{1,\dots,N\}$. Assume that each two distinct members intersect in a nonempty arithmetic progression and that the intersection of all members is empty. Let $F_0$ consist of those members containing no seven-term arithmetic progression.

**Theorem.** $|F_0|\le 1+\binom{N}{2}$. In particular, at $N=14$ any such family of size at least 96 has at least four members containing a seven-term progression.

**Exact consequence for every $N\ge1$.** Among admissible families whose members all avoid seven-term progressions, the maximum is

$$
1+\binom N2+\left\lfloor\frac{N-1}{4}\right\rfloor .
$$

In fact, that value remains the maximum if up to $\lfloor(N-1)/4\rfloor$ members may contain seven-term progressions. For a family with empty total intersection, add the permitted number of such members to the theorem's bound. For a family with a common point, apply Yang's starred-family theorem. Szabó's construction attains the displayed value using only sets of size at most five. Families of size zero or one also satisfy the upper bound. [Yang, Theorems 1.2 and 1.4](https://arxiv.org/abs/2607.23004)

## The incidence vectors

For a set $A$, let $u_A$ be its containment indicators for the empty set and the $\binom{N}{2}$ pairs. Let $v_A$ be its containment indicators for singletons and arithmetic progressions of lengths 3, 4, and 6. Write $a_j(S)$ for the number of $j$-term progressions in $S$, and put

$$
q(S)=1+\binom{|S|}{2}-|S|-a_3(S)-a_4(S)-a_6(S).
$$

Counting common coordinates gives $u_A\cdot u_B-v_A\cdot v_B=q(A\cap B)$. On every nonempty finite integer set $S$ with no seven-term progression, $q(S)$ is zero for progressions and strictly positive for all other sets. [Proof of the score inequality](score.md)

Suppose $\sum_{A\in F_0}c_Au_A=0$ is a nonzero real linear relation. For $A\ne B$ in $F_0$, their intersection is a nonempty progression and contains no seven-term progression, so $q(A\cap B)=0$. Squaring the relation yields

$$
0=\left\|\sum_{A\in F_0} c_Av_A\right\|^2+
  \sum_{A\in F_0} c_A^2q(A).
$$

All terms on the right are nonnegative. Thus $\sum c_Av_A=0$, and $c_A=0$ unless $A$ is a progression. Every remaining progression has at most six elements. Extend $c$ by zero to all progressions of lengths 1 through 6.

## Relations among short progressions

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

Set $\alpha_{x,d}=0$ when the corresponding five-term progression does not lie in $[N]$. For a fixed step $d$ the coefficient of the pair $\{u,u+2d\}$ is $\alpha_{u,d}+\alpha_{u+2d,d}$, since the two pairs in $w_{x,d}$ are $\{x-2d,x\}$ and $\{x,x+2d\}$, both with sign $+1$. No other step contributes to a pair of that span.

In any residue class modulo $2d$ with nonzero coefficients $\alpha_{x,d}$, take the first and last such centres $p,q$. Then the pairs $\{p-2d,p\}$ and $\{q,q+2d\}$ have nonzero coefficients and must belong to $F$. They would be disjoint if $p<q$. Pairs arising from different residue classes would also be disjoint. Thus for each step with a nonzero coefficient there is exactly one active centre, and both pairs at that centre belong to $F$.

If two or more steps are active, they contribute at least four distinct pairwise intersecting pairs. To see that these pairs share a vertex, take two of them, $xy$ and $xz$. The only pair missing $x$ and meeting both is $yz$, and no fourth distinct pair meets all three edges of that triangle. At every active step the two pairs meet only at their centre. Hence all active steps have the same centre $x$. For a single active step this also holds.

Take the least active step $d$ at $x$. Its five-term progression $P$ has nonzero coefficient $\alpha_{x,d}$. Its middle triple $M=\{x-d,x,x+d\}$ occurs with sign $+1$ in $h(P)$. Its only other possible contribution comes from the outer triple of step $d/2$, which is inactive or nonintegral. Its coefficient is therefore $\alpha_{x,d}$. Thus $P,M\in F$. Choose $B\in F$ omitting $x$. To meet the two forced pairs, $B$ must contain both endpoints of $P$. The only progression in $P$ containing both endpoints and omitting $x$ is the pair of endpoints. Therefore $B\cap P=\{x-2d,x+2d\}$ and $B\cap M=\varnothing$, contradicting the pairwise intersection hypothesis.

The vectors $u_A$ are therefore independent in dimension $1+\binom{N}{2}$, proving the theorem.

## Families with few members omitting one point

**Proposition.** Suppose some $x\in[N]$ is omitted by at most $\lfloor(N-1)/4\rfloor+1$ members of a family with pairwise nonempty progression intersections. Then

$$
|F|\le 1+\binom N2+\left\lfloor\frac{N-1}{4}\right\rfloor.
$$

Put $H=1+\binom N2$, $k=\lfloor(N-1)/4\rfloor$ and $s=\min(x-1,N-x)$. For a family all of whose members contain $x$, Yang proves the point-dependent bound $H+\lfloor s/2\rfloor\le H+k$. This settles the case where no member omits $x$. [Yang, proof of Theorem 1.4 following Theorem 5.3](https://arxiv.org/html/2607.23004v1#S5)

Let $r\ge1$ be the number of members omitting $x$, let $C$ be their common intersection, and put $D=[N]\setminus(C\cup\{x\})$, $m=|D|$. Delete these $r$ members. Adjoin the singleton $\{x\}$ and all pairs $\{x,u\}$ with $u\in D$. Each new set was absent because some deleted member misses it. Its intersection with every remaining member contains $x$ and has size at most two. Thus the resulting family is admissible and has size $|F|-r+1+m$. The point-dependent bound gives

$$
|F|\le H+\lfloor s/2\rfloor+r-1-m.
$$

This proves the claim if $r\le m+1$. Otherwise $r\ge2$ and $m\le r-2\le k-1$. The intersection $C$ is the intersection of all pairwise intersections of the deleted members. It has $N-1-m\ge N-k>\lceil N/2\rceil$ points (here $k\ge1$). A nonempty intersection of arithmetic progressions is an arithmetic progression, since each nonsingleton progression is an interval in one residue class. Thus $C$ is a progression, and its size forces its step to be 1. This interval lies on one side of $x$, so all points on the other side belong to $D$, giving $s\le m$. It follows that $|F|\le H+\lfloor m/2\rfloor+r-1-m\le H+k$.

## Independent check at fourteen points

Checking consecutive gaps identifies each arithmetic progression, counting singletons and pairs as progressions. The verifier enumerates all $2^{14}-1$ nonempty subsets. Of these, 752 contain a seven-term progression. On the other 15,631, it checks the score inequality directly. [Verifier](rank.cpp)

Run these commands from this directory with a C++20 compiler.

```sh
c++ -std=c++20 -O2 -Wall -Wextra -pedantic rank.cpp -o /tmp/erdos272-rank14
/tmp/erdos272-rank14
```
