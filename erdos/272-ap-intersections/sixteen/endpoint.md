# Singleton intersections at both endpoints

Can an AP-intersecting family of 125 subsets of $[16]$ avoid having pairs of sets that meet *only* at an endpoint ($1$ or $16$)? No: in fact, both endpoints must appear as singleton intersections multiple times over.

**Proposition.** Any admissible family of 125 subsets of $[16]$ must contain three disjoint pairs of members whose intersection is exactly $\{1\}$—meaning six distinct members witness those three intersections. By reflection ($i \mapsto 17 - i$), the same holds for $\{16\}$.

More generally, any admissible family of size $f \ge 125$ contains at least $\lceil (f - 120)/2 \rceil$ disjoint pairs intersecting in $\{1\}$ (and likewise for $\{16\}$).

## The big idea

Think about what happens if we delete the endpoint $1$ from every set in a family $F$ of size 125, trying to shrink $F$ down to an admissible family on the 15-point ground set $\{2, \ldots, 16\}$. We already know the exact maximum on 15 points is $t(15) = 109$ ([fifteen-point proof](../fifteen/)).

Why doesn't deleting $1$ immediately work? Removing the endpoint $1$ from any arithmetic progression of length at least two simply shortens it by one term and preserves its common difference—so intersections of size $\ge 2$ stay valid nonempty progressions! Only two things can go wrong:

1. **Emptied intersections:** Two sets $A, B \in F$ whose intersection was *just* $\{1\}$ become disjoint after $1$ is deleted.
2. **Duplicate pairs (collisions):** Two distinct sets $P$ and $P \cup \{1\}$ (with $1 \notin P$) collapse to the same set $P$ after $1$ is deleted. Call such a pair $\{P, P \cup \{1\}\}$ a *duplicate pair*, and call $P$ its *duplicate base*. Because $P = P \cap (P \cup \{1\})$, every duplicate base $P$ must be a nonempty progression in $\{2, \ldots, 16\}$.

If we first delete a small set of members to break all $\{1\}$-intersections, then delete $1$ from all remaining sets, and finally merge any colliding duplicate pairs, the surviving family lives on 15 points and can have at most 109 members. Thus, proving that $F$ has **at most 11 duplicate pairs** forces many $\{1\}$-intersections—enough to guarantee three disjoint pairs.

## Step 1: At most eleven duplicate pairs

We first show that no admissible family of 125 subsets of $[16]$ can contain 12 duplicate pairs.

There are exactly **284** nonempty arithmetic progressions $P \subseteq \{2, \ldots, 16\}$ (15 singletons, $\binom{15}{2} = 105$ pairs, and 164 progressions of length three or more). Suppose two distinct progressions $P$ and $Q$ both serve as duplicate bases in $F$, so all four sets $P$, $P \cup \{1\}$, $Q$, and $Q \cup \{1\}$ lie in $F$. Their pairwise intersections impose two compatibility requirements on $P$ and $Q$:

- $P \cap Q$ must be a nonempty arithmetic progression (this also handles $P \cap (Q \cup \{1\})$ and $(P \cup \{1\}) \cap Q$ since $1 \notin P, Q$), and
- $(P \cup \{1\}) \cap (Q \cup \{1\}) = (P \cap Q) \cup \{1\}$ must also be an arithmetic progression.

Form the compatibility graph on the 284 candidate bases using these two conditions as edges. Any collection of 12 duplicate bases in $F$ forms a 12-clique, so it must lie inside some inclusion-maximal clique of size at least 12. There are **5,627** such maximal cliques. The [Python verifier](endpoint.py) enumerates all of them via the Bron–Kerbosch algorithm with pivoting and excludes each one as follows.

Fix a maximal clique $C$ of size $|C| \ge 12$. Choosing 12 bases from $C$ means skipping at most $|C| - 12$ bases of $C$. For every base $P$ that *is* chosen, every member of $F$ must be compatible with both $P$ and $P \cup \{1\}$ (a candidate set is allowed to equal $P$ or $P \cup \{1\}$, since the intersection condition only constrains distinct sets). The verifier therefore runs a branch-and-bound pruning loop:

1. **Filter by skip allowance:** Retain only bit masks (candidate subsets of $[16]$) that fail compatibility with $P$ or $P \cup \{1\}$ for at most $|C| - 12$ bases $P \in C$.
2. **Coloring and omission bounds:** Try to exclude the surviving candidate pool by checking whether it is too small, or whether partitioning candidates into classes of mutually incompatible masks (a proper coloring of the compatibility graph) yields fewer than 125 classes. Apply the same coloring bound to each point's *omission list* (candidates avoiding a given point $x$), which must admit at least 14 mutually compatible members ([proof of the omission bound](general-bound.md)).
3. **Branching on bases:** If the clique survives, branch on an undecided base $P \in C$: either *require* $P$ or *skip* $P$ (decrementing the remaining skip budget in the skip branch) and repeat.
4. **Fixed-base coloring and omission branching:** Once all 12 required bases are fixed, both sets $P$ and $P \cup \{1\}$ for each chosen base are already selected as members of $F$. Subtract these fixed members from the total target of 125 and from each point's omission target of 14, and apply the coloring tests to the remaining candidates. If a node still survives, pick a point's omission list, partition it into independent (mutually incompatible) classes, and discard $t - 1$ classes where $t$ is the number of omissions still required. Because those $t - 1$ classes can supply at most $t - 1$ members, any valid completion must pick at least one mask from the remaining classes. The verifier tries each such remaining mask in turn—keeping its compatible neighbors and discarding only alternatives already explored at that node. At most three such extra choices suffice to rule out every case.

## Step 2: From duplicate pairs to three disjoint $\{1\}$-intersections

Let $F$ be an admissible family of 125 subsets of $[16]$. Form a graph $G_1$ whose vertices are the 125 members of $F$, with an edge between $A$ and $B$ whenever $A \cap B = \{1\}$.

Let $U \subseteq F$ be any *vertex cover* of $G_1$ (a set of vertices touching every edge). Delete every set in $U$ from $F$, and then delete the element $1$ from every remaining set:

- **Every pairwise intersection stays a nonempty progression:** Every pair whose intersection was $\{1\}$ had at least one member in $U$ and was deleted. Every remaining pair either did not contain $1$ in its intersection, or had $1$ as the left endpoint of an arithmetic progression of length $\ge 2$, whose removal leaves a shorter nonempty progression with the same step.
- **At most 11 sets collide:** Any two remaining sets that become equal after deleting $1$ must have formed a duplicate pair $\{P, P \cup \{1\}\}$ in $F$. By Step 1, there are at most 11 such pairs.

Merging duplicates produces an admissible family on the 15-point ground set $\{2, \ldots, 16\}$ of size at least $125 - |U| - 11$. Since $t(15) = 109$ ([fifteen-point proof](../fifteen/)), we obtain
$$
125 - |U| - 11 \le 109 \implies |U| \ge 5.
$$

Now choose any *maximal matching* $M$ in $G_1$ (a collection of pairwise disjoint edges to which no further disjoint edge can be added). The $2|M|$ endpoints of the edges in $M$ form a vertex cover of $G_1$—otherwise an uncovered edge could be added to $M$. Therefore $2|M| \ge 5$, so $|M| \ge 3$. Those three edges give three disjoint pairs of members of $F$ intersecting in $\{1\}$. Applying reflection ($i \mapsto 17 - i$) proves the identical statement for $\{16\}$.

### Extension to families larger than 125

For any admissible family $F$ of size $f \ge 125$, the same duplicate-pair bound still holds: if $F$ had 12 duplicate pairs (24 sets), we could extend them to a 125-member subfamily, contradicting Step 1. Deleting a vertex cover $U$ of $G_1$ and merging at most 11 duplicate pairs now yields
$$
f - |U| - 11 \le 109 \implies |U| \ge f - 120.
$$
Taking a maximal matching $M$ again gives $2|M| \ge f - 120$, hence $|M| \ge \lceil (f - 120)/2 \rceil$ disjoint pairs intersecting in $\{1\}$ (and symmetrically for $\{16\}$).

## Reproduction

Run the following command in this directory with Python 3.10 or later to verify the finite duplicate-pair exclusion:

```sh
python3 endpoint.py
```

The script checks all 5,627 maximal cliques across 10,517 search branches and rules out twelve duplicate pairs.
