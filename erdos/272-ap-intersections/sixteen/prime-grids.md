# A signed rank bound on every integer ground set

In the sixteen-point signed-rank proof ([signed-rank.md](signed-rank.md)), the fact that the Möbius score is strictly positive on every nonprogression is checked finitely on all 65,535 nonempty subsets of $[16]$. Can we achieve the same signed-rank linear independence **algebraically for every $N$**—in fact, on *any* finite set of integers—without any finite computer check?

Yes! The trick is to replace containment of a composite $(d + 1)$-point grid with containment of its individual **prime subdivisions**.

## Setup: prime subdivisions

Let $F$ be a family of distinct subsets of $[N]$ whose pairwise intersections are nonempty arithmetic progressions and whose total intersection is empty ($\bigcap_{A \in F} A = \varnothing$). Everything below works identically on any finite ordered set of integers, indexing endpoints only in that ground set.

For a set $A$ and two points $a < b$ in $A$, define $J_A(a, b)$ to be the set of prime numbers $p$ such that:

1. $p$ divides $b - a$, and
2. $A$ contains all $p + 1$ equally spaced points dividing the interval $[a, b]$ into $p$ equal steps—that is, $a + j \cdot \frac{b - a}{p} \in A$ for every $j = 0, 1, \ldots, p$.

For any squarefree divisor $d \mid (b - a)$, define the indicator coordinate
$$
f_{a,b,d}(A) = 1_{\{a,b\} \subseteq A} \prod_{p \mid d} 1_{p \in J_A(a,b)}.
$$

- If either $a \notin A$ or $b \notin A$, then $f_{a,b,d}(A) = 0$.
- When $d = 1$, the empty product equals $1$, so $f_{a,b,1}(A) = 1_{\{a,b\} \subseteq A}$ simply records whether $A$ contains the pair $\{a, b\}$.
- When $d$ is composite (e.g., $d = 6 = 2 \cdot 3$), $f_{a,b,d}(A)$ tests whether $A$ contains *each* prime subdivision separately, rather than the full $(d + 1)$-point arithmetic progression.

*Concrete example:* Take $A = \{0, 2, 3, 4, 6\}$ with endpoints $a = 0, b = 6$. The 2-subdivision of $[0, 6]$ is $\{0, 3, 6\} \subseteq A$, and the 3-subdivision is $\{0, 2, 4, 6\} \subseteq A$. Thus $J_A(0, 6) = \{2, 3\}$ and $f_{0,6,6}(A) = 1$, even though $A$ does *not* contain the full 7-point grid $\{0, 1, 2, 3, 4, 5, 6\}$.

## Main theorem

**Theorem.** For any admissible family $F$ with empty total intersection, the following real row vectors, indexed by $A \in F$, are linearly independent:

- the constant coordinate $1$;
- every prime-subdivision coordinate $f_{a,b,d}(A)$ where $d \mid (b - a)$ is squarefree and has an **even** number of prime factors ($\omega(d) \in \{0, 2, 4, \ldots\}$, which includes all $\binom{N}{2}$ pair indicators at $d = 1$);
- the equality indicator $1_{A = P}$ for each arithmetic progression $P$ of length $m \ge 3$ such that $m - 1$ is **not squarefree** and $m \ne 5$ (for example, $m = 9, 10, 13, 17, \ldots$).

**Consequence.** Counting active columns (those nonzero on at least one member of $F$) immediately yields
$$
|F| \le 1 + \binom{N}{2} + u + v,
$$
where $u$ is the number of active coordinates $f_{a,b,d}$ with even positive prime-factor count $\omega(d) \ge 2$, and $v$ is the number of progression members of the indicated non-squarefree lengths ($m \ge 3$, $m \ne 5$). Whenever $u + v \le \lfloor (N - 1)/4 \rfloor$, this achieves Szabó's conjectured upper bound (families with a common point already satisfy that bound by [Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004)).

## Why the diagonal score is positive

**The big idea.** In any finite arithmetic progression $S$ of length $m$, exactly $m - 1$ pairs of elements are *consecutive*, so $1 - |S| + (\text{\# consecutive pairs}) = 1 - m + (m - 1) = 0$. What distinguishes a consecutive pair $(a, b)$ of $S$ from a non-consecutive pair $h \ge 2$ steps apart? A non-consecutive pair always has some prime $p \mid h$ whose $p$-subdivision lies inside $S$; a consecutive pair has *none*! Inclusion–exclusion turns "admits no common prime subdivision" into a signed inner product.

For two sets $A, B$ and $a < b$, define the kernel $K_{a,b}(A, B)$ to be $1$ if $\{a, b\} \subseteq A \cap B$ and $J_A(a, b) \cap J_B(a, b) = \varnothing$ (no common prime subdivision between $a$ and $b$), and $0$ otherwise. By inclusion–exclusion over squarefree divisors $d \mid (b - a)$,
$$
K_{a,b}(A, B) = \sum_{d \mid (b - a),\ d\text{ squarefree}} (-1)^{\omega(d)} f_{a,b,d}(A) f_{a,b,d}(B),
$$
where $\omega(d)$ counts the distinct prime factors of $d$. Define the signed bilinear form
$$
Q(A, B) = 1 - |A \cap B| + \sum_{a < b} K_{a,b}(A, B).
$$

- **Off the diagonal ($A \ne B$):** Since $A \cap B$ is a nonempty arithmetic progression, $K_{a,b}(A, B) = 1$ precisely when $a$ and $b$ are *consecutive* elements of $A \cap B$. Indeed, if $a$ and $b$ are $h \ge 2$ steps apart in $A \cap B$, any prime $p \mid h$ yields a full $p$-subdivision inside $A \cap B \subseteq A, B$, so $p \in J_A(a, b) \cap J_B(a, b)$ and $K_{a,b}(A, B) = 0$. Consecutive elements ($h = 1$) admit no prime subdivision at all, giving $K_{a,b}(A, B) = 1$. Since $A \cap B$ has $|A \cap B| - 1$ consecutive pairs,
  $$
  Q(A, B) = 1 - |A \cap B| + (|A \cap B| - 1) = 0.
  $$
- **On the diagonal ($A = B$):** Every pair of consecutive elements of $A$ has no elements of $A$ between them, hence no prime subdivision in $A$, so $\sum_{a < b} K_{a,b}(A, A)$ counts at least all $|A| - 1$ consecutive pairs of $A$.
  - If $A$ is a progression, the same calculation as above gives $Q(A, A) = 0$.
  - If $A$ is **not** a progression, $A$ contains three consecutive elements $x < y < z$ with unequal gaps ($y - x \ne z - y$). Look at the outer pair $(x, z)$: the *only* element of $A$ strictly between $x$ and $z$ is $y$. Any $p$-subdivision of $[x, z]$ requires $p - 1 \ge 1$ interior points, so the only possible prime subdivision inside $A$ would be $p = 2$, forcing $y$ to be the midpoint $(x + z)/2$—impossible since $y - x \ne z - y$. Therefore $J_A(x, z) = \varnothing$, so $K_{x,z}(A, A) = 1$ adds at least $+1$ on top of the $|A| - 1$ consecutive pairs, proving **$Q(A, A) > 0$ for every nonprogression $A$**.

## Why a relation would force a common point

Split the signed coordinates of $Q(A, B)$ by sign:

- Let $u_A$ collect the **positive** coordinates: the constant $1$ and all $f_{a,b,d}(A)$ with $\omega(d)$ even.
- Let $v_A$ collect the **negative** coordinates: the singleton indicators $1_{x \in A}$ and all $f_{a,b,d}(A)$ with $\omega(d)$ odd.

Then $u_A \cdot u_B - v_A \cdot v_B = Q(A, B)$. Suppose the row vectors of the theorem satisfy a real linear relation with coefficients $c_A$ ($A \in F$). Because each progression $P$ of non-squarefree length $m \ge 3$ ($m \ne 5$) has its own equality indicator $1_{A = P}$, we immediately get $c_P = 0$ for all such progressions. Moreover, $\sum_{A \in F} c_A u_A = 0$. Taking the squared Euclidean norm and substituting $u_A \cdot u_B = v_A \cdot v_B + Q(A, B)$—with $Q(A, B) = 0$ for $A \ne B$—gives
$$
0 = \left\|\sum_{A \in F} c_A u_A\right\|^2 = \left\|\sum_{A \in F} c_A v_A\right\|^2 + \sum_{A \in F} c_A^2 Q(A, A).
$$
Since every term on the right is nonnegative, we deduce that:

1. $c_A = 0$ for every nonprogression $A$ (where $Q(A, A) > 0$), so the relation is supported solely on arithmetic progressions;
2. $\sum_{A \in F} c_A v_A = 0$, so the relation annihilates *both* positive and negative signed coordinates; and
3. $c_P = 0$ at every progression $P$ whose length $m \ge 3$ has $m - 1$ non-squarefree and $m \ne 5$.

**Why every remaining progression except length 5 has its own coordinate:** On a progression $P$, $f_{a,b,d}(P)$ agrees with containment of the full $(d + 1)$-point arithmetic grid from $a$ to $b$. Indeed, if $a, b \in P$ are $h$ steps apart in $P$, then $p \in J_P(a, b)$ holds precisely when $p \mid h$. Because $d$ is squarefree, every prime divisor $p \mid d$ divides $h$ precisely when $d \mid h$—which is equivalent to $P$ containing the full $(d + 1)$-point progression from $a$ to $b$.

Thus, for every progression $P$ of length $m$ with $m - 1$ squarefree, the coordinate $f_{\min P, \max P, m - 1}$ (in $u$ or $v$ depending on the parity of $\omega(m - 1)$) acts on progressions as the exact containment indicator $1_{P \subseteq Q}$. Singletons ($m = 1$) are likewise detected by the singleton indicators in $v$. Every surviving progression of length other than 5 therefore indexes its own containment coordinate!

Now subtract $c_P w_{x,d}$ for each five-term progression $P$, where $w_{x,d}$ is the five-term inclusion–exclusion relation from the sixteen-point signed-rank proof ([five-term relations and proof](signed-rank.md#the-five-term-relations)). Each $w_{x,d}$ vanishes on every progression containment coordinate except its own five-term coordinate (which is absent from $(u, v)$), and has $+1$ at $P$. In the resulting remainder, any inclusion-maximal progression with a nonzero coefficient would be detected at its own containment coordinate—impossible.

Hence the relation must be a linear combination of the five-term relations $w_{x,d}$. As shown in [signed-rank.md](signed-rank.md#the-five-term-relations), any nonzero combination forces two pairs $\{x - 2d, x\}, \{x, x + 2d\}$, their five-term progression $P$, and its middle triple $\{x - d, x, x + d\}$ (at the smallest active step $d$) into $F$ around a common centre $x$, contradicting the existence of a member $B \in F$ omitting $x$. That argument uses no upper bound on $N$ and holds on any finite integer ground set. $\square$

### Relation to the sixteen-point profile verifier

On $[16]$, the numerical profile verifier in [signed-rank.md](signed-rank.md) uses containment of the *full* composite $(d + 1)$-point grid (e.g., all 7 points of a 7-term progression) rather than separate prime subdivisions. Its finite verification that $q(S) > 0$ on all 65,205 nonprogressions in $[16]$ licenses discarding a coordinate as soon as the full composite grid fails to appear in $F$. The prime-grid theorem above trades that finite check for an all-$N$ algebraic proof using the explicitly defined coordinates $f_{a,b,d}$. [Sixteen-point score and profile verification](signed-rank.md)
