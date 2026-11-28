# The exact maximum for intersections of at most six terms

We already know that for *every* $N$, capping pairwise intersections at five terms yields the exact maximum $1 + \binom{N}{2} + \lfloor (N - 1)/4 \rfloor$ (which equals 124 at $N = 16$). On sixteen points, we can push this exactness one step further to **six-term** intersections:

**Theorem.** Any family of distinct subsets of $\{1, \ldots, 16\}$ whose pairwise intersections are arithmetic progressions of one through six terms has **at most 124 members**. This bound is attained.

## A family of 124

Szabó's construction achieves 124 using sets of size at most five (so all pairwise intersections actually have at most four terms):

1. Start with all $1 + 15 + \binom{15}{2} = 121$ subsets of $[16]$ of size at most three containing $8$.
2. For each step $d \in \{1, 2, 3\}$, take the five-term progression $P_d = \{8 - 2d, 8 - d, 8, 8 + d, 8 + 2d\}$ centred at $8$—namely $\{6, 7, 8, 9, 10\}$, $\{4, 6, 8, 10, 12\}$, and $\{2, 5, 8, 11, 14\}$.
   - **Remove** its two nonprogression triples passing through $8$ (those with unequal gaps, e.g., $\{6, 8, 9\}$ and $\{7, 8, 10\}$ for $d = 1$).
   - **Add** $P_d$ together with its two four-term ends obtained by dropping either endpoint.

Each step removes 2 sets and adds 3, giving $121 + 3 = 124$ members. Why is every pairwise intersection a progression of at most four terms?

- **Two original sets:** Both contain $8$ and have size $\le 3$, so their intersection contains $8$ and has size $1$ or $2$.
- **An original set and an added set:** Their intersection contains $8$. If it has size $1$ or $2$ it is automatically a progression; if it has size $3$, the original set must be a triple inside $P_d$ that survived removal—meaning it is one of the arithmetic-progression triples of $P_d$.
- **Two added sets at the same step $d$:** They are $P_d$ and its two four-term prefixes/suffixes, so they meet in three or four consecutive terms of $P_d$.
- **Two added sets at different steps $d \ne d'$:** Note that $P_1 \cap P_2 = \{6, 8, 10\}$, $P_1 \cap P_3 = \{8\}$, and $P_2 \cap P_3 = \{8\}$. Every subset of $\{6, 8, 10\}$ containing $8$ is $\{8\}$, $\{6, 8\}$, $\{8, 10\}$, or $\{6, 8, 10\}$—always an arithmetic progression!

[Szabó's construction, §5](https://page.mi.fu-berlin.de/szabo/PDF/aps.pdf) · [Lean verification](Erdos272Sixteen.lean)

## Why 125 is impossible

Suppose a family exceeding 124 existed; passing to a subfamily, fix a family $F$ of **125** subsets of $[16]$ whose pairwise intersections are progressions of lengths one through six. Call a progression of length one through six *short*.

Because any family sharing a common point has size at most 124 ([Yang's starred bound, Theorem 1.4](https://arxiv.org/abs/2607.23004) · [finite star check](general-bound.md#finite-check-for-sixteen-points)), $F$ has **empty total intersection** ($\bigcap_{A \in F} A = \varnothing$).

### Step 1: At least four members come from a list of 101 marked sets

Give each subset $A \subseteq [16]$ two indicator vectors:

- $u_A \in \mathbb{R}^{121}$: the constant $1$ together with the 120 pair-containment indicators;
- $v_A$: the containment indicators of all singletons and all progressions of lengths $3$, $4$, and $6$.

Writing $a_j(S)$ for the number of $j$-term progressions in $S$, counting common coordinates gives
$$
u_A \cdot u_B - v_A \cdot v_B = q(A \cap B), \qquad
q(S) = 1 + \binom{|S|}{2} - |S| - a_3(S) - a_4(S) - a_6(S).
$$

Because every pairwise intersection $A \cap B$ ($A \ne B$) is a *short* progression, and $q(S) = 0$ on every short progression, **every off-diagonal entry $q(A \cap B)$ vanishes automatically** (unlike the unrestricted case in [rank-mark.md](rank-mark.md), no diagonal-dominance weights are needed!). Mark every nonempty subset $A \subseteq [16]$ that is *not* a short progression and has $q(A) \le 0$. Direct enumeration on $[16]$ gives **101 marked sets** (including all 14 seven-term progressions).

Now restrict to the *unmarked* members of $F$. Every unmarked nonprogression has $q(A) > 0$. If the unmarked vectors $u_A$ satisfied a real linear relation $\sum c_A u_A = 0$, squaring and substituting $u_A \cdot u_B = v_A \cdot v_B + q(A \cap B)$ would yield
$$
0 = \left\|\sum c_A v_A\right\|^2 + \sum c_A^2 q(A).
$$
Both terms are nonnegative, so $c$ must vanish outside short progressions and also satisfy $\sum c_A v_A = 0$. The short-progression lemma below shows that no nonzero such relation can hold in a family with empty total intersection. Therefore the unmarked vectors $u_A$ are linearly independent in $\mathbb{R}^{121}$, forcing at least $125 - 121 = 4$ members of $F$ to lie in the 101-set marked list.

### Step 2: No quartet of marks can start a family of 125

Fix a total order on the 101 marked sets. Consider both $F$ and its reflection under $i \mapsto 17 - i$, and choose whichever copy has the lexicographically earlier quartet of its first four marked sets. Then:

1. the chosen quartet is no later than its reflection, and
2. every additional marked set in $F$ comes *after* the fourth mark in the chosen quartet.

Enumerating all pairwise-compatible four-element subsets of the 101 marks (where compatible means their intersection is a short progression) yields **12,245** quartets, of which **13** are fixed by reflection. Taking one canonical representative per reflection orbit leaves
$$
\frac{12{,}245 + 13}{2} = 6{,}129
$$
quartets to test.

All 6,129 quartets are excluded by the same private-triple counting machinery used in the four-element bound:

- Every triple $T = \{a, b, c\}$ ($a < b < c$) spans its progression hull $H(T)$ from $a$ to $c$ with step $\gcd(b - a, c - b)$, and every progression containing $T$ contains $H(T)$. If a member contains $T$ while missing part of $H(T)$, then $T$ is a *private triple* of that member (no second member can contain $T$).
- The verifier counts private triples (with progression cost augmentation) and partitions low-cost candidates into mutually incompatible color classes, each contributing at most one member to $F$.
- Applying this bound first to candidates of size at least five lowers the maximum number of large sets, thereby raising the required number of small sets (size $\le 4$).
- The verifier then temporarily fixes small candidates and nonprogression triples, discarding any whose inclusion makes 125 impossible, and re-checks the remaining pool after exclusions.

This computer-assisted check closes all 6,129 quartets. [Counting inequality](four-or-more.md#excluding-four-element-candidates) · [Integer implementation](private_triples.hpp) · [Quartet search](small_root_search.cpp)

## The short-progression lemma and replay

To confirm that no nonzero linear relation on $(u_A, v_A)$ can be supported on short progressions in $F$, we have both a hand proof ([proof of the lemma by hand](rank-mark.md#relations-among-short-progressions)) and a direct finite mod-2 verification:

- **Pair configurations:** Since a singleton would force a common point, every member in the support has size at least two. Any collection of pairwise-intersecting two-element sets is either a **star** (all sharing one point: 16 choices) or a **triangle** ($\binom{16}{3} = 560$ choices), because the only pair avoiding $x$ that hits both $\{x, y\}$ and $\{x, z\}$ is $\{y, z\}$.
- **Binary elimination:** For each of the 16 stars and 560 triangles, take its pairs together with all progressions of lengths 3 through 6, and run Gaussian elimination modulo $2$ on the concatenated rows $(u_A, v_A)$. Across all 576 pools, this produces just **16 distinct nonzero binary relations**.
- **Forced common point:** Every one of those 16 relations contains, for some five-term progression $P = \{a, b, x, c, e\}$ (in increasing order), all four sets $P$, $\{a, x\}$, $\{x, e\}$, and the middle triple $\{b, x, c\}$. Any family member $B$ omitting $x$ must contain both $a$ and $e$ to meet $\{a, x\}$ and $\{x, e\}$; the only progression inside $P$ containing both endpoints while omitting $x$ is $\{a, e\}$, leaving $B \cap \{b, x, c\} = \varnothing$—impossible.
- **Why mod 2 rules out real dependence:** If integer rows are linearly dependent over $\mathbb{R}$, they are dependent over $\mathbb{Q}$. Clearing denominators gives a nonzero integer relation, and dividing out the highest common power of $2$ ensures at least one odd coefficient—yielding a nonzero relation modulo $2$.

[Finite rank check](verify_short.py) · [Proof of the lemma by hand](rank-mark.md#relations-among-short-progressions)

### Reproduction

Run the following commands from this directory with Python 3.10 or later and a C++20 compiler to verify the starred bound, the 16 binary relations, and all 6,129 quartets:

```sh
c++ -std=c++20 -O3 small_root_search.cpp -o /tmp/erdos272-roots
python3 verify_short.py --replay /tmp/erdos272-roots
```

To verify the 124-member lower-bound construction in Lean, run:

```sh
lake build
lake env leanchecker --fresh Erdos272Sixteen
```
