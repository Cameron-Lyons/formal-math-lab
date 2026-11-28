# Families with no common point: a general rank bound

When can an arithmetic-progression-intersecting family of subsets of $[N] = \{1, \ldots, N\}$ exceed Szabó's conjectured bound $1 + \binom{N}{2} + \lfloor (N - 1)/4 \rfloor$? Yang proved that families whose members all share a common point can never exceed it. Here we show that any counterexample with *empty* total intersection must rely heavily on **long progressions**: members containing no seven-term progression are bounded unconditionally by $1 + \binom{N}{2}$!

## Main theorem and consequences

Let $F$ be a family of at least two distinct subsets of $[N] = \{1, \ldots, N\}$ such that:
- any two distinct members of $F$ intersect in a nonempty arithmetic progression (counting singletons and pairs as progressions), and
- the total intersection $\bigcap_{A \in F} A$ is empty.

Let $F_0 \subseteq F$ consist of all members containing **no seven-term arithmetic progression**.

**Theorem.**
$$
\lvert F_0\rvert \le 1 + \binom{N}{2}.
$$
In particular, at $N = 14$, any family of size at least $96$ with empty total intersection must contain at least $96 - (1 + \binom{14}{2}) = 96 - 92 = 4$ members containing a seven-term progression.

**Exact consequence for every $N \ge 1$.** Among admissible families in which at most $\lfloor (N - 1)/4 \rfloor$ members contain a seven-term progression (in particular, among all families avoiding seven-term progressions altogether), the exact maximum size is
$$
1 + \binom{N}{2} + \left\lfloor \frac{N - 1}{4} \right\rfloor.
$$
*Why this follows immediately:*
- If $\bigcap_{A \in F} A = \emptyset$ and $\lvert F \rvert \ge 2$, adding the allowed number of seven-term holders to $\lvert F_0 \rvert \le 1 + \binom{N}{2}$ gives the bound.
- If all members share a common point, Yang's starred-family theorem gives the exact same upper bound ([Yang, Theorems 1.2 and 1.4](https://arxiv.org/abs/2607.23004)).
- Families of size $0$ or $1$ trivially satisfy the bound, and Szabó's construction attains it using only sets of size at most $5$.

---

## Proof strategy

We use a signed linear-algebra method (a variant of Fisher's inequality / Babai–Frankl's polynomial method):

1. Assign each member $A \in F_0$ a positive indicator vector $u_A$ of dimension $1 + \binom{N}{2}$ (recording the empty set and all pairs) and a negative indicator vector $v_A$ (recording singletons and progressions of lengths $3, 4, 6$).
2. The difference $u_A \cdot u_B - v_A \cdot v_B$ equals a progression score $q(A \cap B)$ that vanishes on every progression without a 7-term progression and is strictly positive on every nonprogression.
3. Consequently, any real linear dependence $\sum_{A \in F_0} c_A u_A = 0$ forces all nonprogressions to have $c_A = 0$ and forces $\sum c_A v_A = 0$ as well—so $c$ is a dependence on the *concatenated* vectors $(u_A, v_A)$ supported on progressions of lengths $1$ through $6$.
4. The only missing coordinate in lengths $1$–$6$ is length $5$, so $c$ must be a linear combination of explicit inclusion–exclusion vectors $w_{x, d}$ indexed by five-term progressions. Pairwise intersections then force all active five-term progressions to share a single center $x$, and picking a member $B \in F$ omitting $x$ creates an empty intersection—contradiction!

---

## The incidence vectors

For any subset $A \subseteq [N]$:
- Let $u_A \in \{0, 1\}^{1 + \binom{N}{2}}$ be its containment indicators for $\emptyset$ and all $\binom{N}{2}$ two-element subsets of $[N]$.
- Let $v_A$ be its containment indicators for all singletons and all arithmetic progressions of lengths $3$, $4$, and $6$ in $[N]$.

Write $a_j(S)$ for the number of $j$-term arithmetic progressions contained in $S$, and define the score
$$
q(S) = 1 + \binom{\lvert S\rvert}{2} - \lvert S\rvert - a_3(S) - a_4(S) - a_6(S).
$$
Counting coordinates contained in both $A$ and $B$ gives the exact inner-product identity
$$
u_A \cdot u_B - v_A \cdot v_B = q(A \cap B).
$$
A companion proof shows that on every nonempty finite set of integers $S$ containing no seven-term progression, $q(S) = 0$ if $S$ is an arithmetic progression and $q(S) > 0$ otherwise ([Proof of the score inequality](score.md)).

Now suppose for contradiction that there is a nonzero real linear relation $\sum_{A \in F_0} c_A u_A = 0$. For any distinct $A, B \in F_0$, the intersection $A \cap B$ is a nonempty progression containing no seven-term progression, so $q(A \cap B) = 0$. Squaring $\sum_{A \in F_0} c_A u_A = 0$ and rewriting every dot product via $u_A \cdot u_B = v_A \cdot v_B + q(A \cap B)$ gives
$$
0 = \left\| \sum_{A \in F_0} c_A u_A \right\|^2
  = \left\| \sum_{A \in F_0} c_A v_A \right\|^2 + \sum_{A \in F_0} c_A^2 q(A).
$$
Every term on the right-hand side is nonnegative, so both sums vanish:
1. $\sum_{A \in F_0} c_A v_A = 0$, and
2. $c_A = 0$ whenever $q(A) > 0$—that is, whenever $A$ is not an arithmetic progression.

Every surviving member $A \in F_0$ with $c_A \ne 0$ is therefore a progression of length between $1$ and $6$. Extend $c$ by zero to all progressions of lengths $1$ through $6$ in $[N]$.

---

## Relations among short progressions

Let $e_A$ denote the unit basis vector at subset $A$ in the coefficient space. For any five-term progression $P = \{x - 2d, x - d, x, x + d, x + 2d\}$ with center $x$ and step $d$, let $a = x - 2d$, $b = x + 2d$, and let $O = \{a, x, b\}$ be its outer triple. For any set $D$ containing $a$ and $b$, define the inclusion–exclusion combination
$$
h(D) = e_D - e_{D \setminus \{a\}} - e_{D \setminus \{b\}} + e_{D \setminus \{a, b\}},
\qquad
w_{x, d} = h(P) - h(O).
$$

**Why $w_{x, d}$ annihilates every $(u, v)$ coordinate:**
- Evaluating $h(D)$ on the containment coordinate indexed by a set $T$ gives $1$ if $\{a, b\} \subseteq T \subseteq D$, and $0$ otherwise (by inclusion–exclusion on whether $a$ and $b$ are dropped).
- In particular, the empty-set coordinate cancels ($h(D)$ has alternating signs summing to $0$).
- Which progressions $T \subseteq P$ contain *both* endpoints $a$ and $b$? Their step in units of $d$ must divide $4$, leaving only three possibilities: the pair $\{a, b\}$, the outer triple $O$, and $P$ itself!
- Because $\{a, b\}$ and $O$ lie inside both $P$ and $O$, $h(P)$ and $h(O)$ agree on every progression coordinate *except* $T = P$—and $(u, v)$ has **no five-term coordinate**!

Thus every $w_{x, d}$ is a linear relation among the concatenated vectors $(u_A, v_A)$.

Moreover, the *only* five-term progression appearing in $w_{x, d}$ is $P$ itself, with coefficient $+1$. Subtract $c_P w_{x, d}$ from $c$ for every five-term progression $P$. The remainder $c' = c - \sum_{x, d} c_P w_{x, d}$ is still a linear relation on $(u, v)$, supported exclusively on progressions of lengths $1, 2, 3, 4$, and $6$. Each of those lengths *is* itself a coordinate of $(u, v)$! If $c'$ were nonzero, choosing an inclusion-maximal set $T$ with $c'_T \ne 0$ would make the $T$-coordinate of the relation equal to $c'_T \ne 0$, impossible. Hence $c' = 0$, so
$$
c = \sum_{x, d} \alpha_{x, d} w_{x, d}, \qquad \alpha_{x, d} = c_P.
$$

---

## Pairwise intersections force a common centre

Extend $\alpha_{x, d} = 0$ whenever the five-term progression centered at $x$ with step $d$ does not lie inside $[N]$. Call a center $x$ **active** for step $d$ if $\alpha_{x, d} \ne 0$, and call a step $d$ **active** if it has at least one active center. Because $c \ne 0$, at least one step is active.

1. **At most one active center per step $d$.** Expand $w_{x, d} = h(P) - h(O)$ on two-element sets: the pairs inside $P$ with endpoints omitted are $\{x - d, x + d\}$ (which doesn't occur because $a, b$ are removed together, leaving the 3-term middle triple) — specifically, in $h(P)$ every term has size $3, 4$, or $5$, while in $-h(O) = -e_{\{a,x,b\}} + e_{\{x,b\}} + e_{\{a,x\}} - e_{\{x\}}$ the two pairs are $\{x - 2d, x\}$ and $\{x, x + 2d\}$, both with sign $+1$. No other step creates a pair of span $2d$, so the coefficient of any pair $\{u, u + 2d\}$ in $c$ is
   $$
   c_{\{u, u + 2d\}} = \alpha_{u, d} + \alpha_{u + 2d, d}.
   $$
   In any residue class modulo $2d$ containing an active center, let $p$ and $q$ be its *smallest* and *largest* active centers. Then:
   - $c_{\{p - 2d, p\}} = \alpha_{p - 2d, d} + \alpha_{p, d} = \alpha_{p, d} \ne 0$, and
   - $c_{\{q, q + 2d\}} = \alpha_{q, d} + \alpha_{q + 2d, d} = \alpha_{q, d} \ne 0$,

   so both pairs $\{p - 2d, p\}$ and $\{q, q + 2d\}$ must belong to $F$. If $p < q$, those two pairs are disjoint (since $p < q$ implies $p \le q - 2d < q$), contradicting that members of $F$ intersect! Likewise, pairs coming from two different active residue classes modulo $2d$ are disjoint. Thus each active step $d$ has **exactly one** active center $x$, and both forced pairs $\{x - 2d, x\}$ and $\{x, x + 2d\}$ belong to $F$.

2. **All active steps share the same center $x$.** If two or more steps are active, they produce at least four distinct pairs in $F$ (pairs from different steps have different spans $2d$, so they cannot repeat), and every two must intersect. Any intersecting family of $\ge 4$ pairs must form a star sharing one common point: given two intersecting pairs $\{x, y\}$ and $\{x, z\}$, the only pair avoiding $x$ that meets both is $\{y, z\}$, and no fourth distinct pair can meet all three edges of the triangle $\{x, y, z\}$. Since the two forced pairs at each active step meet *only* at their center, every active step must share the exact same center $x$. (For a single active step, this is trivial.)

3. **Contradiction at the smallest active step.** Let $d$ be the **smallest** active step at the common center $x$, with five-term progression $P = \{x - 2d, x - d, x, x + d, x + 2d\}$ and middle triple $M = \{x - d, x, x + d\}$.
   - $P$ has coefficient $\alpha_{x, d} \ne 0$, so $P \in F$.
   - In $w_{x, d} = h(P) - h(O)$, the middle triple $M = P \setminus \{a, b\}$ appears with sign $+1$ inside $h(P)$. The only other vector $w_{x', d'}$ that could ever contribute to a triple centered at $x$ of span $2d$ is the outer triple $O$ of step $d/2$ centered at $x$—which is either inactive (by minimality of $d$) or nonintegral (if $d$ is odd). Hence $c_M = \alpha_{x, d} \ne 0$, so $M \in F$ as well.

   Now use the empty total intersection of $F$: pick some member $B \in F$ with $x \notin B$.
   - To intersect both forced pairs $\{x - 2d, x\}$ and $\{x, x + 2d\}$ without using $x$, $B$ must contain **both** endpoints $x - 2d$ and $x + 2d$.
   - Look at the intersection $B \cap P$: it must be an arithmetic progression inside $P$ that contains both endpoints $x - 2d$ and $x + 2d$ while omitting the midpoint $x$. The *only* such progression inside $P$ is the two-element pair $\{x - 2d, x + 2d\}$!
   - Therefore $B \cap P = \{x - 2d, x + 2d\}$, which misses $x - d$, $x$, and $x + d$ completely—giving $B \cap M = \emptyset$, contradicting that $B$ and $M$ must intersect!

Hence no nonzero linear relation exists among $\{u_A : A \in F_0\}$. Because the ambient space has dimension $1 + \binom{N}{2}$, we conclude $\lvert F_0 \rvert \le 1 + \binom{N}{2}$. $\square$

---

## Families with few members omitting one point

Even without restricting seven-term progressions, a simple replacement trick extends Yang's starred-family theorem to any family in which some point is missed only a few times.

**Proposition.** Suppose some point $x \in [N]$ is omitted by at most $\lfloor (N - 1)/4 \rfloor + 1$ members of an admissible family $F$. Then
$$
\lvert F\rvert \le 1 + \binom{N}{2} + \left\lfloor \frac{N - 1}{4} \right\rfloor.
$$

*Proof.* Put $H = 1 + \binom{N}{2}$, $k = \lfloor (N - 1)/4 \rfloor$, and $s = \min(x - 1, N - x)$ (the distance from $x$ to the closer endpoint of $[N]$). For any family whose members all contain $x$, Yang proves the point-dependent upper bound $H + \lfloor s/2 \rfloor \le H + k$ ([Yang, proof of Theorem 1.4 following Theorem 5.3](https://arxiv.org/html/2607.23004v1#S5)), which immediately settles the case $r = 0$.

Now suppose $r \ge 1$ members omit $x$. Let $C$ be the common intersection of those $r$ deleted members, and let $D = [N] \setminus (C \cup \{x\})$ with $m = \lvert D \rvert$. Perform a trade:
- **Delete** the $r$ members omitting $x$.
- **Add** the singleton $\{x\}$ and all $m$ pairs $\{x, u\}$ for $u \in D$.

None of these $1 + m$ new sets could already be in $F$, because each avoids at least one of the deleted members (every deleted member misses $x$, and for each $u \in D$ some deleted member misses $u$). Moreover, every new set meets every surviving set in a subset containing $x$ of size $1$ or $2$ (always a nonempty progression). Thus the traded family is still admissible, every member contains $x$, and its size is $\lvert F \rvert - r + 1 + m$. Applying Yang's point-dependent bound gives
$$
\lvert F\rvert \le H + \left\lfloor \frac{s}{2} \right\rfloor + r - 1 - m.
$$

- **Case 1 ($r \le m + 1$):** Then $r - 1 - m \le 0$, so $\lvert F \rvert \le H + \lfloor s/2 \rfloor \le H + k$.
- **Case 2 ($r \ge m + 2$):** Since $r \le k + 1$, we have $r \ge 2$ and $m \le r - 2 \le k - 1$ (forcing $k \ge 1$). Because $C$ is the intersection of all pairwise intersections among the $r \ge 2$ deleted members—and any nonempty intersection of arithmetic progressions is again an arithmetic progression (each nonsingleton progression is an interval inside one residue class)—$C$ is an arithmetic progression of size
  $$
  \lvert C\rvert = N - 1 - m \ge N - k > \left\lceil \frac{N}{2} \right\rceil.
  $$
  A progression with more than half of $[N]$ must have step $1$, so $C$ is a consecutive integer interval! Since $x \notin C$, the entire interval $C$ lies strictly on one side of $x$, which means *every* point on the opposite side of $x$ must lie in $D$, giving $s \le m$. Substituting $s \le m$ yields
  $$
  \lvert F\rvert \le H + \left\lfloor \frac{m}{2} \right\rfloor + r - 1 - m \le H + k,
  $$
  since $\lfloor m/2 \rfloor - m \le 0$ and $r - 1 \le k$. $\square$

---

## Independent check at fourteen points

Checking consecutive gaps tests whether a set is an arithmetic progression (with singletons and pairs accepted). The C++20 verifier enumerates all $2^{14} - 1 = 16{,}383$ nonempty subsets of $[14]$: $752$ contain a seven-term progression, and on all remaining $15{,}631$ subsets it verifies directly that $q(S) = 0$ on progressions and $q(S) > 0$ on nonprogressions. [Verifier](rank.cpp)

Run from this directory with a C++20 compiler:

```sh
c++ -std=c++20 -O2 -Wall -Wextra -pedantic rank.cpp -o /tmp/erdos272-rank14
/tmp/erdos272-rank14
```
