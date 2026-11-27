# A signed rank bound on every integer ground set

Let $F$ consist of distinct subsets of $[N]$ with pairwise nonempty arithmetic-progression intersections and empty total intersection. The following construction gives linearly independent real vectors for its members for every $N$. It also works on any finite ordered set of integers, indexing only endpoints in the ground set.

For $a<b$ in $A$, let $J_A(a,b)$ contain the primes $p$ for which $p\mid(b-a)$ and $A$ contains the $p+1$ equally spaced points from $a$ to $b$. For squarefree $d\mid(b-a)$ put

$$
 f_{a,b,d}(A)=1_{\{a,b\}\subseteq A}\prod_{p\mid d}1_{p\in J_A(a,b)}.
$$

This is zero if either endpoint is absent. At $d=1$ the product is empty and the coordinate records the pair. At composite $d$ it tests the individual prime subdivisions. For example, the integer set $\{0,2,3,4,6\}$ contains both prime subdivisions between 0 and 6. Its seven-point grid is incomplete.

**Theorem.** The following row vectors, indexed by $A\in F$, are linearly independent.

- Include the constant 1 and every $f_{a,b,d}$ for which $d$ has an even number of prime factors.
- Include the equality indicator $1_{A=P}$ for each progression $P$ of length $m\ge3$ such that $m-1$ is not squarefree and $m\ne5$.

In particular $|F|\le 1+\binom N2+u+v$, where $u$ is the number of active coordinates with even, positive prime-factor count, and $v$ is the number of progression members of the indicated nonsquarefree lengths. Here active means nonzero on at least one member. Thus if $u+v\le\lfloor(N-1)/4\rfloor$, the conjectured upper bound holds. Families with a common point satisfy that bound by Yang. [Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004)

## Why the diagonal score is positive

For two sets define $K_{a,b}(A,B)$ to be 1 if both contain $a,b$ and $J_A(a,b)\cap J_B(a,b)$ is empty. Give it value zero otherwise. Inclusion–exclusion gives
$$
K_{a,b}(A,B)=\sum_{d\mid b-a,\ d\text{ squarefree}}
 (-1)^{\omega(d)} f_{a,b,d}(A)f_{a,b,d}(B),
$$
where $\omega(d)$ counts the distinct prime factors. Put
$$
Q(A,B)=1-|A\cap B|+\sum_{a<b}K_{a,b}(A,B).
$$

If $A\cap B$ is a nonempty progression, $K_{a,b}=1$ exactly for consecutive points of that progression. Indeed, if there are $h\ge2$ steps between $a$ and $b$, any prime dividing $h$ gives a full prime subdivision inside the intersection. Consecutive points admit none. Therefore $Q(A,B)=0$ for distinct members.

On the diagonal, $\sum K_{a,b}(A,A)$ counts at least all $|A|-1$ consecutive pairs of $A$. A nonprogression has three consecutive elements with unequal gaps. Their outer pair contributes again: a prime subdivision could use only the middle element, so would have to be the two-step subdivision with equal gaps. Thus $Q(A,A)>0$ for every nonprogression. For progression members the diagonal is zero.

## Why a relation would force a common point

Let $u_A$ collect the positive coordinates of the signed sum (constant included), and $v_A$ the negative coordinates (including the singleton indicators). Then $u_A\cdot u_B-v_A\cdot v_B=Q(A,B)$. A relation on the stated row vectors therefore satisfies
$$
0=\left\|\sum_A c_A v_A\right\|^2+\sum_A c_A^2 Q(A,A).
$$
It annihilates all signed coordinates, is supported on progressions, and has zero coefficients at the equality indicators.

On a progression row, $f_{a,b,d}$ equals containment of the full $d+1$-point grid from $a$ to $b$. In fact, if the progression has $h$ steps between the endpoints, a prime subdivision is present precisely when $p\mid h$. All the prime divisors of squarefree $d$ occur precisely when $d\mid h$. Consequently every progression of an allowed length except five indexes its own containment coordinate. The singleton coordinates handle length one.

Subtract the five-term relations from the sixteen-point signed-rank proof. Each of those relations vanishes on every progression containment coordinate other than its own five-term coordinate. In the remainder, an inclusion-maximal progression with nonzero coefficient would be detected at its own coordinate. Thus only a combination of the five-term relations could survive. Their forced pairs and the middle triple at the smallest active step contradict the existence of a member missing their common centre. That argument works on any finite integer ground set. [Five-term relations and proof](signed-rank.md#the-five-term-relations)

The numerical sixteen-point profile verifier uses full composite-grid containment. Its finite score check licenses discarding a coordinate as soon as the corresponding full grid is absent. The prime-grid theorem instead gives an all-$N$ proof with the explicitly defined coordinates above. [Sixteen-point score and profile verification](signed-rank.md)
