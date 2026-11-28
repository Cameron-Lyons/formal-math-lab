# Families in which one point is omitted infrequently

Yang proved that if every member of an AP-intersecting family $F$ on $[N] = \{1, \ldots, N\}$ contains the same point $x$, then $|F| \le 1 + \binom{N}{2} + \lfloor (N - 1)/4 \rfloor$—matching Szabó's construction. What if a point $x$ is *almost* universal, meaning only a small number of sets in $F$ omit $x$? Here we prove that Szabó's upper bound still holds whenever some point is omitted moderately infrequently, and we verify the sharp threshold of **13 omissions** on $[16]$ by finite search.

**Notation.** Throughout, $F$ is a family of distinct subsets of $[N]$ whose pairwise intersections are nonempty arithmetic progressions. Set
$$
H = 1 + \binom{N}{2}, \qquad k = \left\lfloor \frac{N - 1}{4} \right\rfloor .
$$
For a chosen point $x \in [N]$, write $s = \min(x - 1, N - x)$ for its distance to the nearer endpoint of $[N]$, and let $r$ be the number of members of $F$ that omit $x$.

## General threshold for all $N$

**Theorem.** For every $N \ge 1$, the upper bound $|F| \le H + k$ holds whenever some point $x \in [N]$ is omitted by at most $k + 1 + \lceil 2\sqrt{k + 1} \rceil$ members of $F$. Szabó's construction attains this bound with every member containing the same point.

**The big idea.** Delete the $r$ members omitting $x$ and replace them by $\{x\}$ together with every pair $\{x, y\}$ that avoids their common intersection $C$; the enlarged family is starred at $x$ and hence bounded by Yang's theorem. If $|F| > H + k$, this replacement inequality forces $r$ to exceed the number $m$ of points outside $C \cup \{x\}$ by at least $2$. That forces $C$ to be so large that it must be a contiguous interval on one side of $x$, which in turn severely limits how many distinct omitted subsets can extend $C$ without creating a forbidden intersection crossing $x$.

### Proof of the theorem

For $N = 1, 2$ the maximum sizes are $1$ and $2$ by direct inspection, and for $3 \le N \le 12$ the unconditional exact values establish $|F| \le H + k$ ([Yang, Theorem 1.1](https://arxiv.org/html/2607.23004v1#S1)). Assume henceforth that $N \ge 13$, so $k \ge 3$.

**Step 1: The replacement inequality.** If $r = 0$, every member contains $x$, so Yang's point-dependent starred bound immediately gives $|F| \le H + \lfloor s/2 \rfloor \le H + k$.

Now suppose $r \ge 1$. Let $C = \bigcap \{A \in F : x \notin A\}$ be the common intersection of the $r$ omitted members, and let $m = (N - 1) - |C|$ count the points of $[N] \setminus \{x\}$ lying outside $C$. Delete all $r$ omitted members from $F$, and adjoin:

- the singleton $\{x\}$, and
- all $m$ pairs $\{x, y\}$ with $y \notin C \cup \{x\}$.

None of these $1 + m$ new sets belonged to $F$: $\{x\}$ is disjoint from every omitted member, and for each $y \notin C \cup \{x\}$ there is an omitted member missing both $x$ and $y$, hence disjoint from $\{x, y\}$. Furthermore, every new set contains $x$ and has size at most two, so its intersection with any retained or other new set contains $x$ and has size one or two (automatically a nonempty progression). Applying Yang's point-dependent starred bound to this enlarged family of size $|F| - r + 1 + m$ yields
$$
|F| \le H + \lfloor s/2 \rfloor + r - 1 - m. \tag{1}
$$
This is the replacement argument from the repository's 14-point proof.

Suppose for contradiction that $|F| > H + k$, i.e., $|F| \ge H + k + 1$. Since $s \le \lfloor (N - 1)/2 \rfloor$, we have $\lfloor s/2 \rfloor \le k$, so (1) implies
$$
r \ge m + 2.
$$
In particular $r \ge 2$, which means $C$ equals the intersection of the pairwise intersections of the $r$ omitted members. Each pairwise intersection is a progression. A nonempty intersection of finite arithmetic progressions is again an arithmetic progression, because membership in each progression is defined by a residue class modulo its step together with two endpoint bounds. (And $C$ is nonempty, since $|C| = N - 1 - m \ge N - r + 1 > 0$ under the omission hypothesis below.)

**Step 2: $C$ must be an interval.** Put $J = \lceil 2\sqrt{k + 1} \rceil$. For $k \ge 7$, squaring shows $(k - 1)^2 - 4(k + 1) = k^2 - 6k - 3 > 0$, so $2\sqrt{k + 1} < k - 1$ and hence $J \le k - 1$. That yields $r \le k + 1 + J \le 2k \le \lfloor N/2 \rfloor$. Whenever $r \le \lfloor N/2 \rfloor$, we have
$$
|C| = N - 1 - m \ge N - r + 1 > \lceil N/2 \rceil .
$$
Any arithmetic progression in $[N]$ with step at least $2$ has at most $\lceil N/2 \rceil$ elements, so $C$ must have step $1$—that is, $C$ is a contiguous interval.

What if $r > \lfloor N/2 \rfloor$? Then $k \in \{3, 4, 5, 6\}$, where the upper bounds $k + 1 + J$ on $r$ are $8, 10, 11, 13$, respectively. Since $4k + 1 \le N \le 4k + 4$, checking $k + 1 + J > \lfloor N/2 \rfloor$ leaves only the eight values $N \in \{13, 14, 15, 17, 18, 19, 21, 25\}$. In every one of these eight cases, $|C| \ge N - r + 1 \ge \lfloor N/2 \rfloor$. Suppose $C$ were *not* an interval:

- A progression of step $\ge 3$ has at most $\lceil N/3 \rceil < \lfloor N/2 \rfloor$ points (for instance, at $N = 13$, $\lceil 13/3 \rceil = 5 < 6 = \lfloor 13/2 \rfloor$), so $C$ must have **step 2**.
- Therefore $C$ fills a single parity class with at most one endpoint missing, so its span $[\min C, \max C]$ contains $[3, N - 2]$. Also $|C| \le \lceil N/2 \rceil$, giving $m = N - 1 - |C| \ge \lfloor N/2 \rfloor - 1$.
- Inequality (1) with $|F| \ge H + k + 1$ gives
  $$
  \lfloor s/2 \rfloor \ge m + k + 2 - r = m + 1 - (r - k - 1) \ge \lfloor N/2 \rfloor - J \ge 2
  $$
  (verified across all eight cases: e.g., $6 - 4 = 2$ at $N = 13$). Thus $s \ge 4$, which places $x$ inside $[5, N - 4] \subseteq [3, N - 2] \subseteq [\min C, \max C]$.
- Because $x \notin C$ lies strictly inside the span of the step-2 progression $C$, $x$ has the *opposite parity* to $C$.
- If two omitted members shared *any* point $y$ of the opposite parity to $C$, their intersection would contain $C \cup \{y\}$—hence points of both parities spanning $[\min C, \max C]$—forcing it to be an interval of step $1$ that contains $x$, impossible! Thus each of the $p$ available opposite-parity points (outside $\{x\}$) appears in at most one omitted member.
- Meanwhile, there is at most $h \le 1$ available same-parity point outside $C$. Every omitted member either uses an opposite-parity point (at most $p$ such members) or consists of $C$ plus a subset of the $h$ same-parity points (at most $2^h = h + 1$ such members since $h \le 1$). Thus $r \le p + h + 1 = m + 1$, contradicting $r \ge m + 2$.

Hence in every remaining case $C$ is an interval of at least two consecutive points, and since $x \notin C$, $C$ lies entirely on one side of $x$.

**Step 3: Counting the omitted members.** On the side of $x$ *opposite* to $C$, there are at least $s = \min(x - 1, N - x)$ points; choose $s$ of them. No two omitted members can share any chosen point $y$: otherwise their intersection would contain both $y$ and the consecutive points of $C$, forcing it to be an interval crossing $x$. Discard the at most $s$ omitted members containing a chosen point. The remaining omitted members avoid those $s$ points as well as $x$, leaving at most $t = m - s$ usable positions outside $C$.

Next, consider any remaining omitted member $A$ that is *not* a single contiguous interval. Take the maximal interval in $A$ containing $C$; then $A$ contains some point $z$ outside that maximal interval, separated from $C$ by a missing point $w \notin A$. If a second omitted member also contained $z$, their intersection would contain $z$ and the consecutive points of $C$, forcing it to be an interval spanning across $w$—impossible since $w \notin A$. Thus $z$ is private to $A$. Discard all $b$ noninterval omitted members and reserve one distinct private point for each.

Every surviving omitted member is a contiguous interval extending $C$ using only the $t - b$ unreserved positions. If $\ell$ usable unreserved points lie to the left of $C$ and $h$ to its right, there are at most $(\ell + 1)(h + 1)$ such intervals. Since $\ell + h \le t - b$, AM–GM gives $(\ell + 1)(h + 1) \le g(t - b)$, where
$$
g(u) = \left\lfloor \frac{(u + 2)^2}{4} \right\rfloor .
$$
Because $g(u + 1) - g(u) \ge 1$ for every $u \ge 0$ (as $(u + 3)^2 - (u + 2)^2 = 2u + 5 > 4$), restoring the $b$ noninterval members and the $s$ opposite-side members yields
$$
r \le s + b + g(t - b) \le s + g(t).
$$

**Step 4: Reaching the contradiction.** Set $d = m - \lfloor s/2 \rfloor = t + \lceil s/2 \rceil$, so $0 \le t \le d$ and $s \le 2\lceil s/2 \rceil = 2(d - t)$. Then
$$
r \le 2(d - t) + g(t) = 2d + \bigl(g(t) - 2t\bigr).
$$
The first differences $g(t + 1) - g(t) = 1, 2, 2, 3, 3, \ldots$ are nondecreasing, so $g(t) - 2t$ is discretely convex and attains its maximum on the integer interval $[0, d]$ at one of the endpoints $t = 0$ (giving $2d + g(0) = 2d + 1$) or $t = d$ (giving $g(d)$). Thus
$$
r \le \max\{2d + 1, g(d)\}. \tag{2}
$$

Finally, set $j = r - k - 1$. From (1) and $|F| \ge H + k + 1$, we have $d = m - \lfloor s/2 \rfloor \le r - k - 2 = j - 1$, so $j \ge 1$. From the omission hypothesis, $j \le J = \lceil 2\sqrt{k + 1} \rceil$, which implies $j - 1 < 2\sqrt{k + 1}$, and since $k \ge 3$ we also have $J \le k + 1$. Checking both entries in (2):

- $2d + 1 \le 2(j - 1) + 1 = 2j - 1 < k + 1 + j = r$ (since $j \le k + 1$).
- $g(d) \le g(j - 1) \le (j + 1)^2 / 4$. Since $(j - 1)^2 < 4(k + 1)$, adding $4j$ gives $(j + 1)^2 < 4(k + 1 + j)$, so $(j + 1)^2 / 4 < k + 1 + j = r$.

Both entries in (2) are strictly less than $r$, a contradiction. $\square$

For $N \ge 13$, the only external upper bound used above is the point-dependent estimate in Yang's proof of Theorem 1.4. The earlier repository argument covered up to $k + 1$ omissions. [Yang, §5](https://arxiv.org/html/2607.23004v1#S5) · [Earlier replacement argument](https://github.com/Cameron-Lyons/formal-math-lab/blob/cb3ea3b96b699e62d1a29f2e4e3e0b11cadafccb/erdos-272-fourteen/rank.md#families-with-few-members-omitting-one-point)

## Additional triples for larger ground sets

When $k \ge 7$ (i.e., $N \ge 29$), we can sharpen the replacement step by adjoining not only $\{x\}$ and the $m$ pairs, but also three-term progressions $\{x, x + d, x + 2d\}$ that fit in the gap between $x$ and $C$. This raises the leading constant on the square-root term from $2$ to $\frac{4\sqrt{3}}{3} \approx 2.31$.

**Corollary.** If $k = \lfloor (N - 1)/4 \rfloor \ge 7$, the same upper bound $|F| \le H + k$ holds whenever some point is omitted by at most
$$
k + 1 + \left\lceil \frac{4}{3}\sqrt{3k - 1} \right\rceil
$$
members. (For instance, at $N = 100$ we have $k = 24$, raising the threshold from $k + 1 = 25$ to $25 + \lceil \frac{4}{3}\sqrt{71} \rceil = 37$.)

**Proof.** Suppose to the contrary that $|F| > H + k$, and put $j = r - k - 1$. For $k \ge 7$, checking $9(k - 1)^2 - 16(3k - 1) = 9k^2 - 66k + 25 \ge 4 > 0$ gives $\frac{4}{3}\sqrt{3k - 1} < k - 1$, so $j \le k - 1$ and $r = k + 1 + j \le 2k \le \lfloor N/2 \rfloor$. As in the theorem, (1) forces $m \le r - 2$, so the common intersection $C$ of the omitted sets is an interval with $|C| > \lceil N/2 \rceil$ points.

Reflect $[N]$ if necessary so that $x$ lies to the left of $C$. Because $C$ contains more than half the points of $[N]$ to the right of $x$, the nearer endpoint to $x$ is $1$, so $s = x - 1$. Let $a = \min C - x - 1$ count the gap positions strictly between $x$ and $C$, and let $b = N - \max C$ count the positions strictly to the right of $C$. Then $m = s + a + b$.

**Isolating one omitted member $B_0$:**
- If $a > 0$, then $\min C - 1 \notin C$, so some omitted member $B_0$ misses $\min C - 1$. Let $v$ count the points of $B_0$ lying strictly between $x$ and $C$. Every such point is *private* to $B_0$: if another omitted member shared it, their intersection would be an interval spanning from that point to $C$ across the missing point $\min C - 1$.
- If $a = 0$, pick any omitted member $B_0$ and set $v = 0$.

Set $A = a - v \ge 0$. Delete $B_0$ together with the at most $s$ other omitted members that contain a point to the left of $x$ (as before, no two omitted members can share a point left of $x$). Every remaining omitted member uses at most $A$ positions between $x$ and $C$ and $b$ positions to the right of $C$. Discard each noninterval member and reserve one distinct private point for it, say $u$ on the left of $C$ and $w$ on the right. The surviving interval extensions of $C$ have at most $(A - u + 1)(b - w + 1)$ choices. Restoring the $u + w$ discarded noninterval members yields at most $(A + 1)(b + 1)$ members, because increasing either nonnegative factor by $1$ adds the other factor (at least $1$) to the product. Hence
$$
r \le s + 1 + (A + 1)(b + 1). \tag{3}
$$

**Adjoining disjoint progression triples:** For each $1 \le d \le \lfloor a/2 \rfloor$, consider the three-term progression $T_d = \{x, x + d, x + 2d\}$. Its points $x + d$ and $x + 2d$ lie strictly between $x$ and $C$, so $T_d$ is disjoint from $B_0$ unless one of those two points is among the $v$ private points of $B_0$. Each private point can match $x + d$ for at most one $d$ and $x + 2d$ for at most one $d$—at most two values of $d$ in total. Let $e$ count the triples $T_d$ disjoint from $B_0$. Then $e \ge \lfloor a/2 \rfloor - 2v \ge (a - 1)/2 - 2v$, so $a \le 2e + 4v + 1$ and hence
$$
4A = 4a - 4v = 3a + (a - 4v) \le 3a + 2e + 1 \le 3(a + e) + 1.
$$
All $e$ disjoint triples $T_d$ can be adjoined simultaneously in the replacement argument: each was absent from $F$ (being disjoint from $B_0$), and *every* subset of a three-term progression $\{x, x + d, x + 2d\}$ that contains $x$ is itself an arithmetic progression (of size 1, 2, or 3). Therefore the right-hand side of (1) decreases by $e$.

Write $c = \lceil s/2 \rceil = s - \lfloor s/2 \rfloor$. From $|F| \ge H + k + 1$, the strengthened inequality (1) gives $m - \lfloor s/2 \rfloor + e \le j - 1$. Using $m = s + a + b$ and $4(A + 1) \le 3(a + e) + 5$, we get
$$
c + a + b + e \le j - 1, \qquad
\tfrac{4}{3}(A + 1) + (b + 1) \le (a + e + \tfrac{5}{3}) + (b + 1) \le j - c + \tfrac{5}{3}.
$$
By AM–GM applied to $\frac{4}{3}(A + 1)$ and $(b + 1)$, we have $(A + 1)(b + 1) \le \frac{3}{16}(j - c + \frac{5}{3})^2$. Combined with $s \le 2c$ and (3), this gives
$$
r \le 2c + 1 + \frac{3}{16}\bigl(j - c + \tfrac{5}{3}\bigr)^2.
$$
The right-hand side is a convex quadratic in $c$ on $[0, j - 1]$, so it achieves its maximum at an endpoint:

- At $c = j - 1$: $2(j - 1) + 1 + \frac{3}{16}(\frac{8}{3})^2 = 2j - 1 + \frac{4}{3} = 2j + \frac{1}{3} < k + 1 + j = r$ (since $j \le k - 1$).
- At $c = 0$: $1 + \frac{3}{16}(j + \frac{5}{3})^2 = 1 + \frac{(3j + 5)^2}{48} < k + 1 + j = r$, which rearranges to $9(j - 1)^2 < 16(3k - 1)$ and holds because $j \le \lceil \frac{4}{3}\sqrt{3k - 1} \rceil$.

Both endpoints contradict $r = k + 1 + j$. $\square$

## Finite check for sixteen points

For $N = 16$ ($k = 3$), the general theorem above already covers up to $3 + 1 + \lceil 2\sqrt{4} \rceil = 8$ omissions. A direct finite calculation pushes this all the way to **13 omissions**.

**Proposition.** If some point is omitted by at most 13 members of an admissible family on $[16]$, then the family has size at most 124. Consequently, every point occurs in at most 111 members of any 125-member family.

**Reduction and self-contained star check.** It suffices to rule out families of size exactly 125 (taking a subfamily can only reduce the number of omissions of $x$). At $N = 16$, inequality (1) excludes $r = 1$ (since $r \ge m + 2 \ge 2$) and Yang's theorem excludes $r = 0$. For $r \ge 2$, the common intersection $C$ of the omitted members is either empty or an arithmetic progression. By reflection we may assume $x \in \{1, \ldots, 8\}$.

To keep this finite check completely self-contained, the verifier re-proves the point-dependent starred bound $121 + \lfloor s/2 \rfloor$ for $N = 16$ directly by finite enumeration:

1. Create one class for each of the $1 + 15 + \binom{15}{2} = 121$ sets of size at most three containing $x$.
2. For every nonprogression set $A \ni x$ of size $\ge 4$, verify that some nonprogression triple $T \subset A$ contains $x$ and satisfies $H(T) \not\subseteq A$ (where $H(T)$ is the progression hull of $T$ from $a$ to $c$ with step $\gcd(b - a, c - b)$). Assign $A$ to the class indexed by $T$. No second set containing $T$ can coexist with $A$ in an admissible family, since their intersection would be a progression containing $H(T)$.
3. Match larger *progressions* through $x$ into distinct classes indexed by a nonprogression triple they contain; each of the at most $\lfloor s/2 \rfloor$ unmatched progressions gets its own class.

Since an admissible family uses at most one set per class, every starred family through $x$ has size at most $121 + \lfloor s/2 \rfloor$. [Earlier matching verifier for 13–15](../thirteen/clique_search/verify.cpp)

**Counting exceptional progression triples.** Alongside the singleton $\{x\}$ and the $m$ pairs in (1), adjoin *every* three-term progression $T$ through $x$ that is disjoint from at least one omitted member. Each such triple was absent from the original family, and its intersection with any retained or added set is a subset of $T$ containing $x$—hence always a progression. If there are $e$ such triples, the starred bound at $N = 16$ gives
$$
125 - r + 1 + m + e \le 121 + \lfloor s/2 \rfloor, \qquad
e \le r - m - 5 + \lfloor s/2 \rfloor .
$$

**Search algorithm.** The [finite verifier](verify_near.py) executes the following exhaustive check for each $r$:

1. Enumerate all valid pairs $(x, C)$ with $x \in \{1, \ldots, 8\}$ and $C \subseteq [16] \setminus \{x\}$ empty or a progression, skipping $(x, C)$ if the bound $r - m - 5 + \lfloor s/2 \rfloor$ on $e$ is negative.
2. List all three-term progressions through $x$ disjoint from $C$, and iterate over all choices of an "exception list" of size $\min(r - m - 5 + \lfloor s/2 \rfloor, \text{number of listed triples})$. Any valid omitted family leaves at most that many triples unhit, so its unhit triples are contained in at least one such exception list.
3. For each exception list, enumerate all collections of $r$ mutually compatible supersets of $C$ avoiding $x$ that hit every nonexceptional triple, keeping only those whose common intersection is *exactly* $C$.
4. For each distinct omitted family found, collect all possible retained members—subsets containing $x$ that meet every omitted member in a nonempty progression. A 125-member family now requires a $(125 - r)$-clique in the compatibility graph on that retained list.
5. Check each distinct retained list once per $r$ using a branch-and-bound clique search that greedily partitions vertices into independent color classes (the first $c$ classes can contribute at most $c$ vertices to a clique).

### Reproduction and search totals

Run the check from this directory with Python 3.10 or later (an optional argument sets the maximum $r$ to check):

```sh
python3 verify_near.py
```

For $2 \le r \le 9$, no omitted family survives to the retained-member check. For $r = 10, 11, 12, 13$, the exact counts (after reflecting $x$ into $\{1, \ldots, 8\}$) are:

| Omissions $r$ | Distinct omitted families | Distinct retained-member lists | Required clique size $125 - r$ |
| ---: | ---: | ---: | ---: |
| 2–9 | 0 | 0 | — |
| 10 | 1 | 1 | 115 |
| 11 | 44 | 17 | 114 |
| 12 | 2,865 | 248 | 113 |
| 13 | 125,244 | 3,281 | 112 |

No retained-member list admits the required clique. [Finite verifier](verify_near.py)
