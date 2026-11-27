# Families in which one point is omitted infrequently

Let $F$ be a family of distinct subsets of $[N]$ whose pairwise intersections are nonempty arithmetic progressions. Put $H=1+\binom N2$ and $k=\lfloor (N-1)/4\rfloor$.

**Theorem.** For every $N\ge1$, the upper bound $|F|\le H+k$ holds whenever some point $x$ is omitted by at most $k+1+\lceil 2\sqrt{k+1}\rceil$ members. Szabó's construction attains this bound with every member containing the same point.

**Proof.** The unconditional exact values for $3\le N\le12$ give the result there. For $N=1,2$ the maximum is respectively 1 and 2, by direct inspection. Assume $N\ge13$. [Yang, Theorem 1.1](https://arxiv.org/html/2607.23004v1#S1)

Write $s=\min(x-1,N-x)$ and let $r$ count the members that omit $x$. For $r=0$ apply Yang's point-dependent starred bound $H+\lfloor s/2\rfloor$. For $r\ge1$ let $C$ be the intersection of the omitted members. Write $m=N-1-|C|$. On deleting the $r$ omitted members, adjoin $\{x\}$ and each pair $\{x,y\}$ with $y\notin C\cup\{x\}$. Each new set was absent, being disjoint from an omitted member. Its intersection with each retained set contains $x$ and has size at most two. Applying Yang to the enlarged family gives

$$
|F|\le H+\lfloor s/2\rfloor+r-1-m. \tag{1}
$$

This is the replacement argument in the repository's 14-point proof. Suppose $|F|>H+k$. Since $\lfloor s/2\rfloor\le k$, (1) implies $r\ge m+2$. As $r\ge2$, $C$ equals the intersection of the pairwise intersections of the omitted members. Each pairwise intersection is a progression. A nonempty intersection of finite progressions is a progression, since membership is given by a congruence and two endpoint bounds.

Put $J=\lceil2\sqrt{k+1}\rceil$. For $k\ge7$, squaring gives $2\sqrt{k+1}\le k-1$, so $J\le k-1$. Thus $r\le2k\le\lfloor N/2\rfloor$. Whenever $r\le\lfloor N/2\rfloor$ one has
$$
|C|=N-1-m\ \ge N-r+1>\lceil N/2\rceil,
$$
so $C$ is an interval.

If $r>\lfloor N/2\rfloor$, then $k=3,4,5,6$. At these four values the respective upper bounds on $r$ are $8,10,11,13$. Since $4k+1\le N\le4k+4$, the remaining possibilities for $N$ are $13,14,15,17,18,19,21,25$. In each case $|C|\ge N-r+1\ge\lfloor N/2\rfloor$. If $C$ were not an interval, its step would have to be two, since a progression of larger step has at most $\lceil N/3\rceil<\lfloor N/2\rfloor$ points. Thus it fills a parity class with at most one endpoint missing. The interval from its first to last point contains $[3,N-2]$. Also $m\ge\lfloor N/2\rfloor-1$. Inequality (1) gives $\lfloor s/2\rfloor\ge m+k+2-r\ge\lfloor N/2\rfloor-J\ge2$, placing $x$ inside that interval. If two omitted members shared a point of the opposite parity to $C$, their intersection would have step one and contain $x$. Hence each available opposite-parity point occurs in at most one omitted member. There is at most one same-parity point available outside $C$. If $p$ opposite-parity points and $h\le1$ same-parity points are available, at most $p$ members use the former and at most $2^h=h+1$ members use only the latter. This gives $r\le p+h+1=m+1$, a contradiction.

The interval $C$ contains consecutive points and lies on one side of $x$ in every remaining case.

**Counting the omitted members.** On the opposite side of $x$ choose $s$ points. No two omitted members contain the same chosen point. Their intersection would contain that point and the consecutive points of $C$, hence would be an interval crossing $x$. Discard at most $s$ members that contain a chosen point. There are at most $t=m-s$ remaining positions outside $C$ that can be used.

A remaining member that is not an interval has some point outside its maximal interval containing $C$. If a second omitted member contained this point, their intersection would be an interval extending from $C$ across a missing point of the first member. Thus the point is private to its member. Discard the $b$ noninterval members and reserve one distinct private point for each. The remaining members are intervals extending $C$. If $\ell$ unreserved points lie to its left and $h$ to its right, there are at most $(\ell+1)(h+1)$ possible extensions. As $\ell+h\le t-b$, their number is at most $g(t-b)$, for $g(u)=\lfloor (u+2)^2/4\rfloor$. Since $g(u+1)-g(u)\ge1$, this proves

$$
r\le s+b+g(t-b)\le s+g(t).
$$

Set $d=m-\lfloor s/2\rfloor=t+\lceil s/2\rceil$. Now $s\le 2(d-t)$, and $g(t)-2t$ has nondecreasing first differences. Its maximum on the integer interval $[0,d]$ is attained at an endpoint. Thus

$$
r\le \max\{2d+1,g(d)\}. \tag{2}
$$

Put $j=r-k-1$. From (1) and the presumed violation, $d\le j-1$, so $j\ge1$. From the omission hypothesis, $j\le J\le k+1$, using $k\ge3$. In particular $j-1<2\sqrt{k+1}$. Hence $2(j-1)+1=2j-1<k+1+j$. Also $(j-1)^2<4(k+1)$, which gives $(j+1)^2/4<k+1+j$. Both entries in (2) are therefore strictly less than $r=k+1+j$, a contradiction.

For $N\ge13$ the only external upper bound used is the point-dependent estimate in Yang's proof of Theorem 1.4. The original repo argument gives $k+1$ permitted omissions. [Yang, §5](https://arxiv.org/html/2607.23004v1#S5) · [Earlier replacement argument](https://github.com/Cameron-Lyons/formal-math-lab/blob/cb3ea3b96b699e62d1a29f2e4e3e0b11cadafccb/erdos-272-fourteen/rank.md#families-with-few-members-omitting-one-point)

## Additional triples for larger ground sets

**Corollary.** If $k=\lfloor(N-1)/4\rfloor\ge7$, the same upper bound $H+k$ holds for up to
$$
k+1+\left\lceil\frac43\sqrt{3k-1}\right\rceil
$$
omissions at one point.

Suppose to the contrary that $|F|>H+k$. Write $j=r-k-1$. Since $9(k-1)^2\ge16(3k-1)$ for $k\ge7$, the hypothesis gives $j\le k-1$ and $r\le2k\le\lfloor N/2\rfloor$. As before, (1) implies $m\le r-2$, so the common intersection $C$ of the omitted sets is an interval with more than $\lceil N/2\rceil$ points. Reflect if necessary so $x$ is on the left of $C$. Then $s=x-1$. Let $a=\min C-x-1$ count the positions between $x$ and $C$, and let $b=N-\max C$ count those beyond $C$. Thus $m=s+a+b$.

If $a>0$, choose an omitted member $B_0$ that misses $\min C-1$. It exists because $\min C-1$ lies outside the common intersection. Each of the $v$ points it contains between $x$ and $C$ is private to $B_0$. Sharing such a point would force an interval intersection extending from that point to $C$ across the missing $\min C-1$. If $a=0$, choose any omitted member $B_0$ and set $v=0$. Put $A=a-v$.

Delete $B_0$ and the at most $s$ other omitted members meeting the left side of $x$. Indeed, a point on that side cannot occur in two omitted members, whose intersection would then be an interval through $x$. The remaining members use at most $A$ positions to the left of $C$ and $b$ to its right. Discard each noninterval member and reserve one private point as in the theorem. If $u$ such points are on the left and $w$ on the right, the remaining intervals have at most $(A-u+1)(b-w+1)$ choices. Restoring these $u+w$ members gives at most $(A+1)(b+1)$ members, because increasing either nonnegative side count by one increases the product by at least one. Hence
$$
r\le s+1+(A+1)(b+1). \tag{3}
$$

For $1\le d\le\lfloor a/2\rfloor$, the progression triple $\{x,x+d,x+2d\}$ is disjoint from $B_0$ unless one of its two other points is among those $v$ private points. Each private point accounts for at most two values of $d$. Let $e$ count the disjoint triples. Then $e\ge\lfloor a/2\rfloor-2v$, so $a\le2e+4v+1$ and
$$
4A=4a-4v\le3a+2e+1\le3(a+e)+1.
$$
All $e$ triples can be added in the replacement argument. They were absent from $F$, and any subset of such a triple that contains $x$ is a progression. Therefore the right side of (1) decreases by $e$. Write $c=\lceil s/2\rceil$. The assumed violation now gives
$$
c+a+b+e\le j-1,\qquad
\tfrac43(A+1)+(b+1)\le j-c+\tfrac53.
$$
By (3) and the arithmetic–geometric mean inequality,
$$
r\le 2c+1+\frac3{16}(j-c+\tfrac53)^2.
$$
This upper bound is convex in $c$ on $[0,j-1]$. At $c=j-1$ it equals $2j+1/3<k+1+j$. At $c=0$ it is strictly less than $k+1+j$ because $9(j-1)^2<16(3k-1)$, using $j\le\lceil\frac43\sqrt{3k-1}\rceil$. Both endpoints contradict $r=k+1+j$.

## Finite check for sixteen points

**Proposition.** If some point is omitted by at most 13 members of an admissible family on $[16]$, then the family has size at most 124. Consequently every point would occur in at most 111 members of a 125-member family.

It suffices to test families of exactly 125, since taking a subfamily can only reduce the number of omissions. With $N=16$, (1) excludes $r=1$ and Yang excludes $r=0$. For $r\ge2$ the common intersection $C$ of the omitted members is empty or a progression. Reflection allows us to take $x$ in the first eight positions.

For this finite calculation the program verifies the point-dependent star bound directly. Start one class for each of the 121 sets of size at most three through $x$. For each nonprogression triple $T=\{a,b,c\}$ with $a<b<c$, its hull is the progression from $a$ to $c$ with step $\gcd(b-a,c-b)$. Every progression containing $T$ contains this hull. For each larger nonprogression set $A$ through $x$, the program checks that some such $T\subset A$ contains $x$ and has hull not contained in $A$. Assign $A$ to the class indexed by $T$. Its intersection with another set containing $T$ cannot be a progression, since the intersection would contain the hull. A matching assigns larger progressions through $x$ to distinct classes indexed by a nonprogression triple they contain. Each of the at most $\lfloor s/2\rfloor$ unmatched progressions gets its own class. An admissible family uses at most one set from each class. This supplies the same point-dependent bound for $N=16$ by finite enumeration. [Earlier matching verifier for 13–15](../erdos-272-thirteen/clique_search/verify.cpp)

Alongside the singleton and $m$ pairs in (1), adjoin every progression triple $T$ through $x$ which is disjoint from at least one omitted member. Such a triple is absent from the original family. It intersects each retained or added set in a subset of $T$ containing $x$. Every such subset is a progression, so all these triples may be added together. If there are $e$ of them, Yang gives

$$
125-r+1+m+e\le121+\lfloor s/2\rfloor,\qquad
e\le r-m-5+\lfloor s/2\rfloor.
$$

The verifier enumerates the choices of $x,C$. For each choice it lists the progression triples through $x$ disjoint from $C$. It selects as exceptions any $\min(r-m-5+\lfloor s/2\rfloor,\text{number of listed triples})$ of them, skipping the choice of core if the bound is negative. This includes an exception list containing every triple disjoint from at least one omitted member. For each list it enumerates the $r$ mutually compatible supersets of $C$ avoiding $x$ which meet every nonexceptional triple. It retains only families whose common intersection is exactly $C$.

For each distinct omitted family it lists every possible retained member. These are the subsets containing $x$ which intersect each omitted member in a nonempty progression. A hypothetical family of size 125 now requires a clique of size $125-r$ in the compatibility graph on that list. The clique search greedily partitions vertices into independent color classes. The first $c$ classes contain at most $c$ members of a clique, giving an upper bound for each search branch. Equal lists of possible retained members are tested once for each $r$.

Run the check with Python 3.10 or later from this directory. The optional argument sets the maximum $r$ to check.

```sh
python3 verify_near.py
```

For $2\le r\le9$ no omitted family reaches the retained-member check. For $r=10,11,12,13$, respectively, there are 1, 44, 2,865 and 125,244 distinct omitted families after reflecting $x$ into the first eight positions. The respective counts of distinct lists of retained members are 1, 17, 248 and 3,281. No list admits the required clique. [Finite verifier](verify_near.py)
