# Counting short progressions in an arbitrary set of integers

Why does the signed-rank bound in [rank.md](rank.md) work for sets of *arbitrarily large diameter*? The key ingredient is a purely combinatorial inequality showing that a weighted count of short arithmetic progressions inside any finite set of integers $S$ is always nonnegative, and equals zero **if and only if** $S$ itself is a single arithmetic progression.

## Main inequality

Let $S$ be a finite nonempty set of integers with $m = \lvert S \rvert$, and let $a_j$ denote the number of increasing $j$-term arithmetic progressions contained in $S$.

**Theorem.** For every finite nonempty set $S \subset \mathbb{Z}$,
$$
Q(S) := \binom{m - 1}{2} - a_3 - a_4 - a_6 + a_7
\ \ge\ \left\lfloor \frac{(m - 1)^2}{4} \right\rfloor - a_3 \ \ge\ 0.
$$
In particular, if $S$ contains **no seven-term progression** ($a_7 = 0$), then
$$
q(S) := \binom{m - 1}{2} - a_3 - a_4 - a_6 \ge 0,
$$
with equality **if and only if** $S$ is an arithmetic progression (including singletons and pairs).

*Quick sanity check:* For an arithmetic progression of length $m \in \{1, 2, 3, 4, 5, 6\}$, we have $a_7 = 0$ and the counts $(a_3, a_4, a_6)$ sum to $0, 0, 1, 3, 6, 10$ respectively—matching $\binom{m-1}{2}$ in every case! For the nonprogression triple $S = \{1, 2, 4\}$, $m = 3$ and $a_3 = a_4 = a_6 = 0$, giving $q(S) = \binom{2}{2} = 1 > 0$.

---

## Step 1: Counting maximal runs via an interval forest

**The big idea.** Rewrite $a_3 - a_4$ and $a_6 - a_7$ in terms of *maximal runs* (longest uninterrupted arithmetic progressions of a given step $d$). Every long run of length $\ge 6$ splits into two interleaving even-and-odd runs of step $2d$ whose convex hulls overlap—and those overlaps form a **forest** (acyclic graph), which forces the total number of runs of lengths $3$–$5$ to be at least the number of distinct triple-differences appearing in $S$!

Let us make this exact. For each positive integer step $d$, partition $S$ into residue classes modulo $d$, and inside each residue class split the points into **maximal runs** of consecutive terms with step $d$. Define:
- $H_d$ = number of maximal step-$d$ runs of length $\ge 3$,
- $L_d$ = number of maximal step-$d$ runs of length $\ge 6$.

Because a single run of length $\ell$ contains exactly $\max(0, \ell - j + 1)$ progressions of length $j$ with that step, the telescoping differences $\max(0, \ell - 2) - \max(0, \ell - 3)$ and $\max(0, \ell - 5) - \max(0, \ell - 6)$ simply indicator-count runs of lengths $\ge 3$ and $\ge 6$:
$$
\sum_{d \ge 1} H_d = a_3 - a_4, \qquad \sum_{d \ge 1} L_d = a_6 - a_7.
$$
Now set:
- $R := \sum_{d \ge 1} (H_d - L_d)$, the total number of maximal runs of lengths $3$, $4$, or $5$;
- $D := \{d \ge 1 : H_d > 0\}$, the set of all step sizes that occur in at least one $3$-term progression of $S$.

**Claim:** $R \ge \lvert D \rvert$.

*Proof of claim.* Fix a step $d \ge 1$ and one residue class modulo $d$. Its elements split into two residue classes modulo $2d$ (the even and odd positions along the mod-$d$ grid). Build an intersection graph $G$:
- **Vertices:** For each maximal step-$2d$ run of length $\ge 3$ inside either of these two mod-$2d$ classes, take the closed real interval between its first and last elements. Intervals within the *same* mod-$2d$ class are pairwise disjoint (by maximality).
- **Edges:** Join two intervals (necessarily from opposite mod-$2d$ classes) whenever they intersect.

1. **$G$ is a forest (contains no cycle).** Suppose for contradiction that $G$ had a cycle, and pick the interval $I$ in the cycle with the *smallest right endpoint* $r$. Both neighbors of $I$ in the cycle must intersect $I$ and cannot end before $r$, so both neighbors contain the point $r$! Yet both neighbors belong to the *same* mod-$2d$ class (opposite to $I$'s class), contradicting that intervals from the same class are disjoint.
2. **Each length-$\ge 6$ step-$d$ run yields a distinct edge of $G$.** Take any maximal step-$d$ run of length $\ge 6$ in our mod-$d$ class. Splitting into alternating terms puts at least $3$ points in each of the two mod-$2d$ classes; the two maximal step-$2d$ runs containing those points have overlapping intervals, hence form an edge of $G$.

   Why is this map from runs to edges **injective**? Given an intersecting pair of step-$2d$ runs from opposite classes, every point of the mod-$d$ class lying inside the intersection of their intervals belongs to one of the two runs (since each run is consecutive with step $2d$). Those interleaved points form a consecutive step-$d$ block meeting the interior of the original step-$d$ run, so the edge uniquely recovers the maximal step-$d$ run!

Taking the disjoint union of these forests over all residue classes modulo $d$ produces $L_d$ distinct edges on $H_{2d}$ vertices. Since any forest on $v > 0$ vertices has at most $v - 1$ edges (i.e., $v - e \ge \mathbf{1}_{v > 0}$), we obtain
$$
H_{2d} - L_d \ge \mathbf{1}_{H_{2d} > 0} \qquad \text{for every } d \ge 1.
$$
For odd steps $e$, we trivially have $H_e \ge \mathbf{1}_{H_e > 0}$. Summing $H_{2d} - L_d$ over all $d \ge 1$ and adding $H_e$ over all odd $e \ge 1$ accounts for every $H_k$ exactly once (splitting $k$ into even and odd) and every $L_d$ exactly once:
$$
R = \sum_{k \ge 1} H_k - \sum_{d \ge 1} L_d
  = \sum_{e \text{ odd}} H_e + \sum_{d \ge 1} (H_{2d} - L_d)
  \ge \sum_{e \text{ odd}} \mathbf{1}_{H_e > 0} + \sum_{d \ge 1} \mathbf{1}_{H_{2d} > 0}
  = \lvert D\rvert.
$$

---

## Step 2: Bounding the score and characterizing equality

List the elements of $S$ in increasing order as $s_0 < s_1 < \cdots < s_{m-1}$.

**Center-by-center triple deficits.** Each element $s_i$ has $i$ elements to its left and $m - 1 - i$ to its right, so it can serve as the midpoint of at most $\min(i, m - 1 - i)$ three-term progressions in $S$. Let $\delta_i \ge 0$ be its **deficit** (how many fewer triples are centered at $s_i$ than this ceiling). Summing $\min(i, m - 1 - i)$ over $0 \le i \le m - 1$ gives $\lfloor (m - 1)^2 / 4 \rfloor$, so the total deficit is
$$
\Delta := \sum_{i = 0}^{m - 1} \delta_i = \left\lfloor \frac{(m - 1)^2}{4} \right\rfloor - a_3 \ge 0.
$$

Now focus on the **lower median** $x = s_h$, where $h = \lfloor (m - 1)/2 \rfloor$. Exactly $h - \delta_h$ three-term progressions are centered at $x$, and they all have distinct step sizes, so they contribute $h - \delta_h$ distinct elements to $D$. By Step 1,
$$
R \ge \lvert D\rvert \ge h - \delta_h.
$$
Next, verify the elementary identity (check both even $m = 2h + 2$ and odd $m = 2h + 1$):
$$
\binom{m - 1}{2} = 2 \left\lfloor \frac{(m - 1)^2}{4} \right\rfloor - h.
$$
Substituting $a_3 + a_4 + a_6 - a_7 = 2a_3 - (a_3 - a_4) + (a_6 - a_7) = 2a_3 - R$ turns $Q(S)$ into
$$
Q(S) = \binom{m - 1}{2} - 2a_3 + R
     = 2\Delta + R - h
     \ge 2\Delta - \delta_h
     \ge \Delta
     \ge 0,
$$
where the final step uses $\delta_h \le \Delta$. This proves the main inequality!

### Equality case ($Q(S) = 0$)

Suppose $Q(S) = 0$ and $m \ge 3$ (singletons and pairs are trivially progressions). Then every inequality in the chain above must be tight:
- $\Delta = 0$, so **every** element $s_i$ attains its maximum possible count $\min(i, m - 1 - i)$ of centered triples;
- $R = \lvert D \rvert = h$.

Let $T = \{x - s_i : 0 \le i < h\}$ be the set of the $h$ left-hand distances from the lower median $x = s_h$.

1. **Every triple step lies in $T$.** Because $x$ achieves zero deficit ($\delta_h = 0$), all $h$ elements of $T$ occur as step sizes of triples centered at $x$, so $T \subseteq D$. Since $\lvert T \rvert = h = \lvert D \rvert$, we have $T = D$.
2. **$T$ is closed under positive differences.** Pick any $a < b \le x$ in $S$. Because $b$ sits at or to the left of the median, its maximum centered-triple count is its number of left neighbors; attaining zero deficit means *every* element $a < b$ has a mirror partner $2b - a \in S$, forming a triple of step $b - a$. Hence $b - a \in D = T$. Since the elements of $T$ are precisely the distances $x - a$ for $a < x$, taking $a < b < x$ shows $(x - a) - (x - b) = b - a \in T$.
3. **The left half is evenly spaced.** Let $d = \min T$. Repeatedly subtracting $d$ from any element of $T$ stays inside $T$ until reaching $d$, so every element of $T$ is a multiple of $d$, and the $h$ distinct elements of $T$ must be $T = \{d, 2d, \ldots, hd\}$.
4. **The right half finishes the progression.** Every left element $x - td$ ($t \in T$) has a mirror partner $x + td \in S$, accounting for $2h + 1$ points forming an arithmetic progression of step $d$.
   - If $m = 2h + 1$ is odd, these are *all* points of $S$, so $S$ is an arithmetic progression.
   - If $m = 2h + 2$ is even, there is exactly one remaining point $x + r$ with $r > 0$ and $r \notin T$. For any $x < a < b$ in $S$, the element $a$ sits on the right half and achieves zero deficit on the right, so $b - a \in D = T$. Applying this to $x + d$ and $x + r$ gives $\lvert r - d \rvert \in T = \{d, 2d, \ldots, hd\}$. Thus $r$ is a positive multiple of $d$ at most $(h + 1)d$; since $r \notin T$, we must have $r = (h + 1)d$, so $S$ is again an arithmetic progression!

Finally, when $a_7 = 0$ we have $q(S) = Q(S)$, and as checked above, every progression of length $1$ through $6$ gives $q(S) = 0$. This establishes both directions of the equality criterion. $\square$
