# Bounds for families with short intersections

Let $t_L(N)$ denote the largest size when every intersection of two distinct members is a nonempty progression of at most $L$ terms. Put $H=1+\binom N2$ and $k=\lfloor(N-1)/4\rfloor$. For every positive $N$ the first five values are

| Maximum intersection length $L$ | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: |
| $t_L(N)$ | $N$ | $H$ | $H$ | $H+k$ | $H+k$ |

For $L=1$, take the singleton $\{x\}$ and all pairs through $x$. For the upper bound let the family have at least two members and take their point-incidence vectors. Their Gram matrix has every off-diagonal entry equal to one and diagonal entries $|A|$. Its quadratic form is $(\sum c_A)^2+\sum (|A|-1)c_A^2$. Every member is nonempty, and at most one is a singleton. Thus a zero of this form forces all coefficients to vanish. There are at most $N$ independent vectors.

For $L=2,3$, all sets of size at most three containing a fixed point attain $H$. For the upper bound it suffices to allow three-term intersections. Denote by $a_3(S)$ the number of three-term progressions contained in $S$. The score $q_3(S)=\binom{|S|-1}{2}-a_3(S)$ is nonnegative and vanishes precisely on progressions of at most three terms. Indeed, in the increasing ordering of $m$ points the point with $i$ predecessors can centre at most $\min(i,m-1-i)$ triples. Summing gives $a_3\le\lfloor(m-1)^2/4\rfloor<\binom{m-1}{2}$ for $m\ge4$. The cases $m\le3$ follow directly.

Use a positive vector consisting of the constant and the pair indicators, and a negative vector of singleton and three-term progression indicators. The difference of the two inner products on $A,B$ is $q_3(A\cap B)$. Squaring any relation on the positive vectors, as in the proof below, shows that its coefficients vanish outside progressions of at most three terms and that it annihilates both sets of coordinates. Each remaining set indexes its own containment coordinate. An inclusion-maximal set with nonzero coefficient would be detected by that coordinate. This proves independence in dimension $H$, including for families with a common point. A family with at most one member satisfies the bound directly.

## Exact maximum when intersections have at most five terms

For every $N\ge1$, among families whose pairwise intersections are nonempty progressions of at most five terms, the exact maximum is
$$
1+\binom N2+\left\lfloor\frac{N-1}{4}\right\rfloor .
$$
The same maximum holds with four in place of five. There is no bound on the size of a family member. Szabó's construction attains the formula using distinct sets of size at most five. Two such sets cannot have five common points. Yang gives the matching upper bound whenever the whole family has a common point. [Szabó, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) · [Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004)

For the remaining case, let $F$ be an admissible family with empty total intersection, and let $G\subseteq F$ have all its pairwise intersections of length at most five. We prove the stronger bound $|G|\le H=1+\binom N2$, even if $G$ itself has a common point. Families of size at most one satisfy the bound directly.

For a nonempty integer set $S$ of size $m$, let $a_j(S)$ count its $j$-term progressions. Write
$$
q_5(S)=\binom{m-1}{2}-a_3(S)-a_4(S).
$$
The general score inequality gives $q_5(S)=Q(S)+a_6(S)-a_7(S)$, where $Q(S)\ge0$ and $Q(S)=0$ implies $S$ is a progression. The difference $a_6-a_7$ counts maximal runs of at least six terms, summed over all steps. If $S$ is a progression of length at least six, the run along its own step contributes at least one. Directly on progressions of lengths one through five, $a_3+a_4$ takes the values $0,0,1,3,6$. Consequently $q_5$ is nonnegative, and vanishes exactly on progressions of at most five terms. [General score inequality and equality proof](https://github.com/Cameron-Lyons/formal-math-lab/blob/cb3ea3b96b699e62d1a29f2e4e3e0b11cadafccb/erdos-272-fourteen/score.md)

Give each $A\in G$ a vector $u_A$ consisting of the constant and all pair-containment indicators, and a vector $v_A$ of singleton, three-term and four-term progression containment indicators. Counting common coordinates gives $u_A\cdot u_B-v_A\cdot v_B=q_5(A\cap B)$. For distinct $A,B\in G$ this is zero. A relation $\sum c_Au_A=0$ therefore gives
$$
0=\Big\|\sum c_Av_A\Big\|^2+\sum c_A^2q_5(A).
$$
The coefficients vanish outside progression members of lengths at most five and annihilate both sets of coordinates. Every such progression except a five-term one indexes its own coordinate. Apply the five-term relation argument to these coefficients. Any nonzero relation would force two pairs $\{a,x\},\{x,b\}$, their five-term progression, and its middle triple into $G$. Choose $B\in F$ omitting $x$. It must contain $a,b$ to meet both pairs. Its intersection with the five-term progression can then only be $\{a,b\}$, making it disjoint from the middle triple. This is impossible in $F$. Thus the $u_A$ are independent in dimension $H$. [Five-term relations and forced pairs](signed-rank.md#the-five-term-relations)

More generally, join members of $F$ by an edge whenever their intersection has at least six terms. Deleting any vertex cover leaves a subfamily of size at most $H$, so every cover has size at least $|F|-H$. The endpoints of a maximal matching form a cover. On sixteen points, any family of size 125 would therefore contain two disjoint pairs of members whose intersections each have at least six terms. This argument applies to unrestricted admissible families with empty total intersection.

### Allowing one six-term progression as an intersection

Suppose every intersection has at most six terms and there is at most one distinct six-term intersection $P$. Arbitrarily many pairs may have this same intersection. The exact maximum is again Szabó's formula for every $N$.

To see this when $P$ occurs, add its containment indicator to the negative coordinates $v_A$ above. The new diagonal score is $q_5(A)-1_{P\subseteq A}$. It remains nonnegative. If $P\subseteq A$, the maximal run in $A$ extending $P$ contributes at least one to $a_6(A)-a_7(A)$. Equality therefore requires $Q(A)=0$, which, as proved below, forces $A$ to be a progression of at most seven terms. All off-diagonal scores vanish, including at $P$ itself.

Besides progressions of at most five terms, the only possible zero-score rows are $P$ and a seven-term progression extending $P$ by one point at either end. In fact, any six-term progression inside a seven-term progression uses its step and six consecutive points. Give each such seven-term extension an equality coordinate among the positive columns. There are at most two. In a relation these equality coordinates kill the seven-term coefficients, and $P$ now has its own negative containment coordinate. Subtracting the five-term relations leaves no other possible relation, by the same forced-pair argument. This gives at most $H+2$ members when the total intersection is empty. For $N\ge9$, $2\le\lfloor(N-1)/4\rfloor$. For smaller $N$ the unrestricted exact values give the result directly, with $N=1,2$ immediate. [Yang, Theorem 1.1](https://arxiv.org/abs/2607.23004)

### Several distinct six- or seven-term intersections

**Corollary.** Suppose all pairwise intersections have at most seven terms, and $t$ distinct six- or seven-term progressions occur as intersections. For a family with empty total intersection,
$$
|F|\le H+2t.
$$
Thus Szabó's upper bound holds whenever $2t\le\lfloor(N-1)/4\rfloor$. This includes the case of intersections of at most six terms, where $t$ counts the distinct six-term intersections.

**Theorem.** Suppose $F$ has empty total intersection and all pairwise intersections have at most seven terms. Take a nonempty collection $W$ of six-term progressions that includes every realized six-term intersection and at least one six-term window from every realized seven-term intersection. Put $s=|W|$. Group the windows by their step $d$ and the residue of their first point modulo $d$. Write $g$ for the number of nonempty groups. Within each group, order the starts along the line of step $d$. A block is a maximal sequence of starts spaced exactly $d$ apart. Let $c_i$ be the number of blocks in line $i$ and $c=\sum_i c_i$. Then
$$
|F|\le H+s-g+\sum_i\min(2c_i,5)\le H+s-g+2c.
$$
If $W$ contains the left six-term window of every realized seven-term intersection, then the sharper bound $|F|\le H+s+c$ also holds. To deduce the corollary, take $W$ to consist of every realized six-term progression and the left six-term window of every realized seven-term progression. Then $c\le s\le t$. If neither length occurs, the five-term theorem gives $H$.

**Proof.** For a member $A$, consider its maximal runs of consecutive points with a fixed positive step $d$, separately for each step. A window of step $d$ contained in $A$ lies in a unique such run. Delete any member having two windows from different blocks in the same run. The windows contained in a particular run form an interval in the ordered list of windows on that line. Thus a deleted member can be charged to two consecutive blocks on the line, since it contains the whole progression from the last window of the first block to the first window of the second. This progression has at least eight points. Two members containing it would violate the seven-term intersection hypothesis. There are $c-g$ consecutive pairs of blocks on all the lines, so at most $c-g$ members are deleted.

For every pair of windows with consecutive starts in a block, take the seven-term progression obtained by their union. Let $K$ be the set of these $s-c$ progressions. Each is determined uniquely by the two windows it contains. Starting from the positive and negative coordinates for $q_5$, add a negative containment coordinate for each $P\in W$ and a positive containment coordinate for each $R\in K$. The resulting score is
$$
q_*(S)=q_5(S)-\#\{P\in W:P\subseteq S\}+\#\{R\in K:R\subseteq S\}.
$$
On an intersection of at most five terms it vanishes by the five-term score. A realized six-term intersection belongs to $W$, cancelling $q_5=1$. A realized seven-term intersection also has $q_5=1$. Its only six-term subprogressions are its two consecutive windows. It contains at least one selected window, and if it contains both then it belongs to $K$. Thus every off-diagonal score vanishes.

In any surviving member $A$, the selected windows in one maximal run are either absent or drawn from just one block. If the run contains $h>0$ windows, their starts are consecutive, so it contains exactly $h-1$ of the corresponding progressions in $K$. Summing over steps and runs gives
$$
\#\{P\in W:P\subseteq A\}-\#\{R\in K:R\subseteq A\}
\le a_6(A)-a_7(A),
$$
since the right side counts all maximal runs of length at least six. Consequently $q_*(A)\ge Q(A)\ge0$. As shown below, $Q(A)=0$ requires a progression of at most seven terms.

For a six-term zero-score member, the progression itself must belong to $W$ and therefore indexes a containment coordinate. A seven-term zero-score member must contain at least one selected window. Those with two selected windows already index positive coordinates in $K$. Any with just one extends the first window of a block to the left or the last window to the right. There are at most $2c_i$ such progressions on line $i$. The ones present as members must intersect pairwise. As intervals of seven points spaced $d$ apart on the line, their starts lie in seven consecutive grid positions. Three consecutive starts cannot all occur. If they did, the intersections of the first two and the last two members would force both six-term windows of the middle member into $W$. At most five positions can be selected from seven without selecting three consecutive ones. Add one positive equality coordinate for each such member actually present, equal to one on that member alone. These coordinates preserve the vanishing of the off-diagonal scores and can only increase the diagonals. In any relation among the positive rows, squaring now forces every nonzero coefficient to lie on an original zero-score progression and also annihilate the negative coordinates. The equality coordinates force all singly covered seven-term coefficients to vanish. Every remaining possible support progression except a five-term one indexes its own containment coordinate. Subtracting the five-term relations and using an omitting member from the original $F$ rules out any dependence, exactly as in the five-term proof. The surviving rows are independent in at most $H+(s-c)+\sum_i\min(2c_i,5)$ positive coordinates. Restoring the at most $c-g$ deleted members proves the first bound.

For the sharper bound let $m$ be the actual number of deleted members, each charged to a different gap between consecutive blocks. Write $j$ for the first start of the block on the right of a charged gap and $d$ for its step. The seven-term progression $R$ starting at $j-d$ extends that block to the left. The member $B$ charged to the gap contains $R$ and has at least eight elements. If $R$ were another member, $B\cap R=R$ would be a realized seven-term intersection. Its left six-term window would then belong to $W$, contradicting the gap immediately before $j$. Thus each charge rules out one distinct outward extension from the $2c$ possible equality coordinates. There are at most $2c-m$ of these coordinates, so the original family has size at most $H+(s-c)+(2c-m)+m=H+s+c$.

## Intersections of at most seven terms

Let $F$ be an admissible family on $[N]$ with empty total intersection and at least two members. Suppose that each pair of distinct members intersects in an arithmetic progression of at most seven terms. A member itself may be arbitrarily large. Let $M$ have one row for each member and one column for each seven-term progression $P$ contained in some member, with entry $1$ when $P\subseteq A$ and $0$ otherwise. Then

$$
|F|\le 1+\binom N2+\operatorname{rank}_{\mathbb R} M.
$$

In particular, if at most $k=\lfloor(N-1)/4\rfloor$ distinct seven-term progressions occur across the family, then $|F|\le1+\binom N2+k$. With the two restrictions on intersections and progressions, this bound is sharp for every $N$ when families with a common point are also allowed. Yang bounds the families with a common point and Szabó's attaining family uses sets of size at most five. [Yang, Theorems 1.2 and 1.4](https://arxiv.org/abs/2607.23004)

## The score

Let $a_j(S)$ count the $j$-term progressions in $S$, and for nonempty $S$ put
$$
Q(S)=\binom{|S|-1}{2}-a_3(S)-a_4(S)-a_6(S)+a_7(S).
$$
The general score inequality in the earlier fourteen-point argument proves $Q(S)\ge0$, and shows that $Q(S)=0$ implies that $S$ is an arithmetic progression. In fact its zeros are precisely the progressions of length at most seven. For lengths one through six this is the earlier computation. At length seven the four progression counts $a_3,a_4,a_6,a_7$ are $9,5,2,1$, giving $Q=0$. [General score inequality and equality argument](https://github.com/Cameron-Lyons/formal-math-lab/blob/cb3ea3b96b699e62d1a29f2e4e3e0b11cadafccb/erdos-272-fourteen/score.md)

For the remaining direction it suffices to consider $S=[m]$, since an affine copy gives the same progression counts. We give the strictness detail using the notation of that score proof. Write $H_d$ and $L_d$ for the numbers of maximal runs of step $d$ with lengths at least three and at least six, respectively. Put $D=\{d:H_d>0\}$ and $R=\sum_d(H_d-L_d)$. For an interval of length $m$, all the centre deficits in the score proof vanish, so $Q([m])=R-|D|$. In the decomposition
$$
R=\sum_{d\text{ odd}}H_d+\sum_{d\text{ even}}(H_d-L_{d/2}),
$$
each summand is at least $1$ for $d\in D$ and is nonnegative otherwise, by the run-count inequality in that proof. When $m\ge8$ the odd difference $3$ contributes at least two, since the maximal runs containing $1,4,7$ and $2,5,8$ are distinct. Thus $Q([m])>0$.

## Independence

For each $A$, form $u_A$ from the constant $1$, its 2-set containment indicators, and its row of $M$. Let $v_A$ record containment of singletons and progressions of lengths $3,4,6$. Counting common coordinates gives
$$
u_A\cdot u_B-v_A\cdot v_B=Q(A\cap B).
$$
For distinct $A,B\in F$ the right side vanishes. As in the sixteen-point signed-rank argument, a relation $\sum c_Au_A=0$ implies
$$
0=\Big\|\sum c_Av_A\Big\|^2+\sum c_A^2 Q(A).
$$
It therefore annihilates both sets of coordinates and is supported on progression members of length at most seven. Among these lengths only five lacks a containment coordinate. The five-term inclusion–exclusion relations in the signed-rank proof span all remaining relations: subtract the corresponding relation for each five-term progression and test a maximal remaining support member at its own coordinate. The argument there uses only the forced pairs, the five-term progression and its middle triple to show that a nonzero relation forces a common point. It applies verbatim for every $N$. Hence the $u_A$ are independent. Their rank is at most the number of constant and pair coordinates plus the rank of $M$, as claimed. [Five-term relations and the common-point argument](signed-rank.md#the-five-term-relations)
