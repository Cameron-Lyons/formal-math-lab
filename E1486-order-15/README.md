# Equation 1486 finite magma spectrum (orders 12, 14, 15, 17, and 26)

A **finite magma** of order $n$ is simply a set of $n$ elements equipped with an $n \times n$ multiplication table $a \star b$, with no associativity or commutativity assumed. The **finite spectrum** of an equational law is the list of finite sizes $n$ that admit at least one such table obeying the law for all choices of elements.

In the [Equational Theories Project](https://teorth.github.io/equational_theories/), **Equation 1486** (`E1486`) is the law

$$
x = (y \star x) \star \bigl(x \star (z \star z)\bigr)
$$

for all $x, y, z$ — written in ETP notation as `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`. Reversing every product ($a \star b \mapsto b \star a$, i.e., transposing the multiplication table) gives its opposite-operation **dual equation**, **Equation 2126**, which automatically has the exact same spectrum.

Previously, five finite orders — **12, 14, 15, 17, and 26** — remained unresolved for Equation 1486 and Equation 2126. This Lean 4 project settles all five:

* **Orders 12, 14, and 15:** **no** finite magma satisfies Equation 1486.
* **Orders 17 and 26:** explicit finite magmas **do** satisfy Equation 1486, verified directly by Lean's kernel with no SAT solver and no external imports.

## At a glance

| Order | Result | Lean theorem | Build command | Trust boundary |
| --- | --- | --- | --- | --- |
| 12 | No model | `E1486.Order12.noTable` ([Simple/Order12/NoTable.lean](Simple/Order12/NoTable.lean)) | `lake build Simple.Order12.NoTable` | Kernel reduction + 48 SAT/LRAT checks (`bv_decide` / native evaluation) |
| 14 | No model | `E1486.Order14.noTable` ([Simple/Order14/NoTable.lean](Simple/Order14/NoTable.lean)) | `lake build Simple.Order14.NoTable` | Kernel reduction + 63 SAT/LRAT checks (`bv_decide` / native evaluation) |
| 15 | No model | `E1486.Simple.noTable` ([Simple/NoTable.lean](Simple/NoTable.lean)) | `lake build +Simple.NoTable` | Kernel reduction + 36 SAT/LRAT checks (`bv_decide` / native evaluation) |
| 17 | Model exists | `E1486.Order17.exists_table` ([Simple/Order17.lean](Simple/Order17.lean)) | `lake build Simple.Order17` | Pure Lean kernel check (all $17^3 = 4,913$ triples; `propext` only) |
| 26 | Model exists | `E1486.Order26.exists_table` ([Simple/Order26.lean](Simple/Order26.lean)) | `lake build Simple.Order26` | Pure Lean kernel check (all $26^3 = 17,576$ triples; `propext` only) |

| Field | Summary |
| --- | --- |
| Problem | Equational Theories Project Equation 1486 (opposite dual Equation 2126), finite magma spectrum (`Timeroot/equational_theories` remaining small orders `[12, 14, 15, 17, 26]`) |
| Law | `x = (y ◇ x) ◇ (x ◇ (z ◇ z))` |
| Spectrum status | Together with the ETP fork's proved bounds (no model at 2, 3, 5, 6, 7, 8, 10; model at all other orders outside `{12, 14, 15, 17, 26}`), the finite orders with no model of Equation 1486 are 2, 3, 5, 6, 7, 8, 10, 12, 14, and 15. The two developments are checked separately, not as one combined Lean theorem. |
| Prior art | Checked 22-24 November 2026: no earlier proof or model was found for orders 12, 14, 15, 17, or 26 (bounded search, not a claim of absolute priority). |

## Background and overview

The [E1486 research notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md#remaining-small-orders) (revision `6a653268`) and live spectrum catalogue list orders 12, 14, 15, 17, and 26 as the five unresolved finite orders for Equation 1486 and its dual Equation 2126. Below are walkthroughs of all five proofs:

* [Order 15 exclusion](#order-15-no-model-with-15-elements) — algebraic graph reduction + double-counting bounds + 36 SAT/LRAT refutations
* [Order 12 exclusion](#no-model-with-12-elements) — 49 square patterns, 48 SAT/LRAT refutations (no counting bounds or extra symmetry breaking needed)
* [Order 14 exclusion](#no-model-with-14-elements) — 64 square patterns with lexicographic leader-swap symmetry breaking, 63 SAT/LRAT refutations
* [Order 17 model](#a-model-with-17-elements) — explicit $17 \times 17$ multiplication table, kernel-verified
* [Order 26 model](#a-model-with-26-elements) — explicit $26 \times 26$ multiplication table built via the graph reduction, kernel-verified

**Terminology and notation:**

* For any element $x$, write $x^2 = x \star x$. A **square** is a value that appears on the diagonal of the multiplication table, and $Q = \{x^2\}$ is the set of distinct squares, with $k = |Q|$.
* A **SAT/LRAT refutation** encodes a finite combinatorial search as a Boolean satisfiability (SAT) formula, uses a SAT solver to produce a step-by-step proof of unsatisfiability in LRAT (Linear Resolution Asymmetric Tautology) format, and checks that proof mechanically with a verified proof checker—so the solver itself does not need to be trusted.

## Order 15: no model with 15 elements

The theorem `E1486.Simple.noTable` proves that no binary operation on 15 elements satisfies $(y \star x) \star (x \star (z \star z)) = x$ for all $x, y, z$.

**The big idea.** Searching directly over $15 \times 15$ multiplication tables means fighting $15^{225}$ possibilities. Notice, however, that the variable $z$ in Equation 1486 only appears through its *square* $z^2$. Instead of tracking the full table, we pass to a **directed graph** on the 15 elements whose arrows record right-multiplication by squares (plus $b^2 \to b$). That throws away almost all of the table while keeping enough algebraic rigidity to force every pair of vertices to have at most one two-step path between them, and every vertex to reach every square in two steps. A clean double-counting argument then traps the number of squares $k$ in $4 \le k \le 11$, collapsing the entire search to just **36** Boolean graph-existence problems on 225 binary variables each, which Lean refutes via checked SAT certificates.

### Step 1: Three equalities (and why $k \ge 4$)

Fix any square $q = t^2$, pick any element $x$, and set $u = x \star q$. Substituting into $(y \star x) \star (x \star z^2) = x$ produces three workhorse identities:

$$
x^2 \star u = x, \qquad u \star q^2 = q, \qquad u^2 \star q = u.
$$

Each takes a single substitution:

1. Plugging $(x, y, z) = (x, x, t)$ gives $(x \star x) \star (x \star t^2) = x$, which is $x^2 \star u = x$.
2. Plugging $(x, y, z) = (q, x, t)$ gives $(x \star q) \star (q \star t^2) = q$, which is $u \star q^2 = q$.
3. Plugging $(x, y, z) = (u, u, q)$ gives $u^2 \star (u \star q^2) = u$, and substituting the second equality turns this into $u^2 \star q = u$.

**Immediate lower bound ($k \ge 4$).** Fix one square $q$. The ordered pair of squares $(x^2, u^2)$ uniquely determines $x$: its second coordinate recovers $u = u^2 \star q$ (third equality), and its first coordinate then recovers $x = x^2 \star u$ (first equality). Thus $x \mapsto (x^2, (x \star q)^2)$ maps the 15 elements injectively into $Q \times Q$, forcing $15 \le k^2$ and hence $k \ge 4$.

### Step 2: Replace the multiplication table by arrows

Build a directed graph on the elements of the magma by drawing:

* an arrow $a \to a \star q$ for every element $a$ and every square $q \in Q$, and
* an arrow $b^2 \to b$ for every element $b$.

Count duplicate arrows between the same ordered pair only once (loops $a \to a$ are allowed). A **two-step route** is a directed walk $a \to i \to b$ of length 2, with repeated vertices allowed.

These arrows satisfy three structural rules (valid at any order $n$):

1. **At most one two-step route between any two endpoints.**
   First, every arrow $a \to i$ implies $a = t \star i$ for some element $t$: take $t = a^2$ when $i = a \star q$ (by the first equality $a^2 \star (a \star q) = a$), and take $t = i$ when $a = i^2$ (since $i \star i = a$). Now fix the destination $b$ and consider two cases:
   * *Case A: $b = v \star r$ for some element $v$ and square $r$.* Then the third equality gives $b^2 \star r = b$, so the extra arrow $b^2 \to b$ already comes from right-multiplying by a square. Every arrow $i \to b$ therefore has the form $b = i \star q$ for some square $q$. Writing $a = t \star i$, the defining law gives

     $$
     a \star b = (t \star i) \star (i \star q) = i.
     $$

     Hence $a$ and $b$ uniquely determine the middle vertex $i$ (in fact, $i = a \star b$).
   * *Case B: no such $v, r$ exist.* Then the only arrow entering $b$ is $b^2 \to b$, so every two-step route ending at $b$ must pass through $i = b^2$.

2. **Every vertex reaches every square in two steps.**
   For any vertex $a$ and square $q$, the route $a \to a \star q \to q$ always exists: the first arrow multiplies by $q$, and the second multiplies $u = a \star q$ by the square $q^2$, landing at $u \star q^2 = q$ (second equality).

3. **Every vertex has a square pointing to it.**
   Explicitly, $b^2 \to b$.

**Recognizing squares from arrows alone.** A vertex $b$ is a square if and only if it has a closed two-step route $b \to i \to b$. Every square reaches itself in two steps by rule 2. Conversely, given any closed route $b \to i \to b$, the proof of rule 1 forces $i = b^2$ in both Case A ($i = b \star b$) and Case B (the sole incoming arrow to $b$ is $b^2 \to b$). Reading the same closed route shifted by one step as $i \to b \to i$ gives $b = i^2$, proving $b$ is a square.

### Step 3: Why there are at most eleven squares ($k \le 11$)

Suppose for contradiction that a 15-element model has $k \ge 12$ squares. Let $d$ and $D$ be the smallest and largest out-degrees (numbers of outgoing arrows) among the 15 vertices.

* **Trapping $d$ and $D$.** We must have $d \le 3$: if every vertex had at least $4$ outgoing arrows, any starting vertex would have at least $4 \cdot 4 = 16$ two-step routes, which by rule 1 must lead to 16 distinct endpoints—impossible on 15 vertices. Conversely, we must have $D \ge 4$, because $3 \cdot 3 = 9$ endpoints cannot reach $k \ge 12$ squares (contradicting rule 2).

* **Double-counting three-step routes into a square.** Fix any vertex $x$ and any square $q$, and count three-step routes $x \to y \to z \to q$ in two ways:
  * *By the first arrow ($x \to y$):* each out-neighbor $y$ of $x$ has a *unique* two-step route to $q$ (existence by rule 2, uniqueness by rule 1), so the total number of three-step routes equals the out-degree of $x$.
  * *By the last arrow ($z \to q$):* a **predecessor** $z$ of $q$ (a vertex with an arrow $z \to q$) contributes 1 route if $x$ reaches $z$ in two steps and 0 otherwise (by rule 1). So the total equals the number of predecessors of $q$ reachable from $x$ in two steps.

  Choosing $x$ to be a vertex of maximum out-degree $D$ proves that **every square $q$ has at least $D$ predecessors**.

* **The bottleneck inequality.** Now pick a vertex $x_0$ of minimum out-degree $d$. For each square $q$, exactly $d$ of its predecessors are reached from $x_0$ in two steps, leaving at least $D - d$ predecessors of $q$ *missed* by $x_0$. Every missed vertex must be a **nonsquare** (by rule 2, $x_0$ reaches every square in two steps). Counting arrows from missed vertices into squares in two ways gives:
  * at least $D - d$ incoming arrows per square $\implies$ at least $k(D - d)$ arrows;
  * at most $15 - k$ missed vertices (all nonsquares), each with at most $D$ outgoing arrows $\implies$ at most $(15 - k)D$ arrows.

  Hence

  $$
  k(D - d) \le (15 - k)D.
  $$

* **Closing the contradiction.** Substituting $k \ge 12$ and $d \le 3$ gives $12(D - 3) \le 3D$, i.e., $D \le 4$. Combined with $D \ge 4$, this forces $D = 4$, $d = 3$, and $k = 12$, with **equality** throughout:
  * each of the $15 - 12 = 3$ nonsquares sends all $4$ of its outgoing arrows into squares, and
  * each square has exactly $4$ predecessors in all (3 reached from $x_0$ plus 1 missed).

  Finally, pick any nonsquare $u$ and any square $q$ that it points to ($u \to q$). By our first count, there are $\operatorname{outdeg}(u) = 4$ three-step routes from $u$ to $q$. Yet $q$ has only $4$ predecessors in total, one of which is $u$ itself—and since $u$ is a nonsquare, $u$ cannot reach itself in two steps. That leaves at most $3$ reachable predecessors for the last arrow, a contradiction. Therefore $k \le 11$.

### Step 4: The remaining 36 finite checks at order 15

We are left with $4 \le k \le 11$. Setting $x = q$ in the second equality ($u \star q^2 = q$, where $u = q \star q = q^2$) gives $(q^2)^2 = q$ for every square $q$. Thus squaring acts as an involution on the $k$ squares: it fixes $j$ squares ($q^2 = q$) and swaps the remaining $k - j$ squares in $(k - j)/2$ pairs. For example, $k = 4$ allows $j \in \{0, 2, 4\}$ (3 patterns). Summing over $k = 4, 5, \ldots, 11$ yields

$$
3 + 3 + 4 + 4 + 5 + 5 + 6 + 6 = 36 \quad \text{cases.}
$$

Each case fixes only the pattern $(k, j)$ and asks whether any $15 \times 15$ zero-one adjacency matrix $A$ (225 Boolean variables, loops allowed) satisfies all four graph conditions, where $B = A^2$ counts two-step routes ($B_{ab} = (A^2)_{ab}$):

1. Every entry of $B$ is at most 1.
2. Exactly the designated squares have $B_{qq} = 1$, and for each such $q$ the unique closed two-step route is $q \to q^2 \to q$ using the partner fixed by the pattern $(k, j)$.
3. For each designated square $q$, every entry in column $q$ of $B$ equals 1.
4. Every column of $A$ has a 1 in at least one square's row.

**Symmetry breaking without losing counterexamples.** Relabeling vertices of a graph never changes whether it obeys the four conditions, so a naive search wastes effort revisiting isomorphic copies of the same partial graph. To break symmetry safely:

1. Put the $k$ squares first, listing the $j$ fixed points before the $(k - j)/2$ swapped pairs.
2. Among the finitely many valid labelings preserving this square pattern, pick one whose square-to-square adjacency entries (read row by row as a bitstring) are **largest in dictionary order** ($1 > 0$).
3. Keeping the squares fixed, sort the nonsquares in decreasing dictionary order of their arrow patterns: first their incoming arrows from squares, then their outgoing arrows to squares.

Because *every* hypothetical valid graph can be relabeled into this canonical form, adding the resulting ordering constraints to the SAT formula cannot discard a counterexample. Lean formally proves this reduction before checking the 36 SAT instances.

For each case, Lean's `bv_decide` tactic obtains a refutation from the bundled SAT solver and verifies it with a formally verified LRAT proof checker. Because the checker executes via native evaluation, Lean's compiler and runtime sit inside the trust boundary. Together, the 36 checked refutations rule out every 15-element table.

## No model with 12 elements

The theorem `E1486.Order12.noTable` proves that no binary operation on 12 elements satisfies Equation 1486.

Because the three arrow rules and $(q^2)^2 = q$ hold at any size, a 12-element table would yield a 12-vertex directed graph with $k$ squares placed first—$j$ fixed points followed by $(k - j)/2$ consecutive swapped pairs. Since $k - j$ is even and $0 \le j \le k \le 12$, there are **49** patterns $(k, j)$.

At order 12 we need neither the counting bounds nor symmetry-breaking ordering constraints. For each pattern, Lean proves no 12-vertex graph meets all four conditions:

* Some square points to each vertex.
* Each square $q$ has a unique closed two-step route, $q \to q^2 \to q$, through its assigned partner; nonsquares have none.
* Every vertex reaches every square in two steps.
* No two distinct vertices share both a predecessor and a successor (which would create two routes between the same endpoints).

The pattern with no squares ($k = 0$) fails the first condition immediately. The other **48** patterns are refuted by SAT/LRAT certificates checked as before.

**File layout.** The order-12 proof spans four short files plus two size-independent shared files:

* [Simple/Graph.lean](Simple/Graph.lean) (shared): derives the arrow rules from Equation 1486 at any size.
* [Normalize.lean](Normalize.lean) (shared): puts the squares in standard $(k, j)$ order.
* [Simple/Test.lean](Simple/Test.lean): states the four graph conditions for any size.
* [Simple/TestOfLaw.lean](Simple/TestOfLaw.lean): proves that arrows from a relabeled table satisfy them.
* [Simple/Order12/Cases.lean](Simple/Order12/Cases.lean): refutes the 49 patterns.
* [Simple/Order12/NoTable.lean](Simple/Order12/NoTable.lean): combines them into `E1486.Order12.noTable`.

Prior art (checked 23 November 2026): no earlier exclusion or model at order 12 was found. The research notes and live spectrum data list 12 as unresolved; their recorded solver runs stopped at 60 or 900 seconds (apart from one restricted family), and a Mace4 run reported on the Lean Zulip stopped after 14 hours.

## No model with 14 elements

The theorem `E1486.Order14.noTable` proves that no binary operation on 14 elements satisfies Equation 1486.

A 14-element table would give a 14-vertex graph satisfying the same four conditions under one of the **64** patterns $(k, j)$ with $0 \le j \le k \le 14$ and $k - j$ even. Unlike order 12, the bare graph conditions are too slow at order 14: in a trial run, 27 of the 63 patterns with a square remained undecided after a minute each.

**Lexicographic leader-swap symmetry breaking.** To break symmetry cleanly and with a shorter Lean proof than at order 15, read a fixed list of arrows as a single bitstring: first the square-to-square arrows row by row, then for each nonsquare its incoming arrows from squares followed by its outgoing arrows to squares. Among the finitely many valid tables with squares first in pattern $(k, j)$, pick one whose bitstring is **largest in dictionary order**.

Any relabeling that keeps the pattern produces another valid table and therefore cannot strictly increase this bitstring. We enforce non-increase for four kinds of elementary swaps:

* two consecutive squares fixed by squaring;
* the two squares of a swapped pair;
* two consecutive swapped pairs;
* two consecutive nonsquares.

Each swap keeps the squares first and commutes with squaring on the squares, so it preserves the pattern. Every pattern has at most 13 such swaps—fewer constraints than in the order-15 proof—and maximizing a single bitstring simplifies the existence proof (which Lean proves for tables of any size).

The pattern with no squares fails the first condition outright. With these swap constraints added, the other **63** patterns are refuted by SAT/LRAT certificates checked as before.

**File layout.** Reusing [Simple/Test.lean](Simple/Test.lean) and [Simple/TestOfLaw.lean](Simple/TestOfLaw.lean) from order 12, the order-14 proof adds:

* [Simple/Leader.lean](Simple/Leader.lean): states the swap conditions.
* [Simple/LeaderOfLaw.lean](Simple/LeaderOfLaw.lean): proves every valid table can be relabeled to satisfy them.
* [Simple/Order14/Cases.lean](Simple/Order14/Cases.lean): refutes the 64 patterns.
* [Simple/Order14/NoTable.lean](Simple/Order14/NoTable.lean): proves `E1486.Order14.noTable`.

Prior art (checked 24 November 2026): no earlier exclusion or model at order 14 was found. The research notes and live spectrum data list 14 as unresolved, recording only one solver run stopped after 60 seconds.

## A model with 17 elements

Order 17 goes the other way: a 17-element magma **does** satisfy Equation 1486. [Simple/Order17.lean](Simple/Order17.lean) gives an explicit $17 \times 17$ multiplication table, and Lean checks all $17^3 = 4,913$ instances of the law directly inside its kernel. This verification uses no SAT certificate, no native evaluation, and no imports (`E1486.Order17.exists_table`, depending only on `propext`).

Prior art (checked 23 November 2026): no earlier 17-element model was found. The research notes and live spectrum data list 17 as unresolved, recording only one solver run stopped after 60 seconds.

## A model with 26 elements

Order 26 also admits a model. [Simple/Order26.lean](Simple/Order26.lean) gives an explicit $26 \times 26$ multiplication table, and Lean verifies all $26^3 = 17,576$ instances of Equation 1486 directly inside its kernel—again with no SAT certificate, no native evaluation, and no imports (`E1486.Order26.exists_table`, depending only on `propext`). The table has 6 squares, 2 of them fixed by squaring.

**From arrows back to a multiplication table.** This model was found by running the graph test above on 26 vertices with square pattern $(k, j) = (6, 2)$. The arrow reduction is reversible: any directed graph obeying the four conditions produces a valid Equation 1486 magma by setting $a \star b$ to the unique middle vertex on the two-step route $a \to i \to b$ whenever one exists, and otherwise to any square with an arrow to $b$.

Prior art (checked 24 November 2026): no earlier 26-element model or exclusion was found. The research notes and live spectrum data list 26 as unresolved, recording three restricted searches (each refuted) and one unrestricted solver run stopped after 60 seconds.

## Reproduce

Build with the pinned Lean 4.36.0 toolchain and its bundled SAT solver. From this directory, run:

```sh
# Order 15 exclusion (36 SAT/LRAT refutations)
lake build +Simple.NoTable

# Order 12 exclusion (48 SAT/LRAT refutations; ~6-8 minutes on desktop)
lake build Simple.Order12.NoTable

# Order 14 exclusion (63 SAT/LRAT refutations; ~13 minutes on desktop)
lake build Simple.Order14.NoTable

# Order 17 model (kernel check, a few seconds)
lake build Simple.Order17

# Order 26 model (kernel check, a few seconds)
lake build Simple.Order26
```

A plain `lake build` checks all five settled orders in this directory.

To inspect the axioms of each theorem:

```sh
printf '%s\n' 'import Simple.NoTable' '#print axioms E1486.Simple.noTable' | lake env lean --stdin
printf '%s\n' 'import Simple.Order12.NoTable' '#print axioms E1486.Order12.noTable' | lake env lean --stdin
printf '%s\n' 'import Simple.Order14.NoTable' '#print axioms E1486.Order14.noTable' | lake env lean --stdin
printf '%s\n' 'import Simple.Order17' '#print axioms E1486.Order17.exists_table' | lake env lean --stdin
printf '%s\n' 'import Simple.Order26' '#print axioms E1486.Order26.exists_table' | lake env lean --stdin
```

The three exclusions use Lean's standard logical axioms plus the native-evaluation axioms for their SAT/LRAT checks (36, 48, and 63 checks respectively), with no admitted lemmas. The order-17 and order-26 models depend only on `propext`.

To read the order-15 Lean proof, start with [Simple/NoTable.lean](Simple/NoTable.lean), which combines the graph reduction, the two counting bounds, and the finite exclusions. The three equalities are `recover_source`, `return_to_square`, and `recover_target` in [E1486.lean](E1486.lean); [Simple/Graph.lean](Simple/Graph.lean) derives the arrow rules from them; [Simple/FiniteBase.lean](Simple/FiniteBase.lean) encodes each graph condition.

## Attribution and license

The square-row identity used in the reduction also appears in the [Equational Theories Project's E1486 notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md). This directory keeps its [Apache-2.0 license](LICENSE) and the copyright notice of the Equational Theories Project contributors.
