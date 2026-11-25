# Equation 1486 finite magma spectrum (orders 12, 14, 15, 17, and 26)

Lean 4 proofs settling the five previously unresolved finite orders (12, 14, 15, 17, and 26) for Equation 1486 (`E1486`, dual Equation 2126) of the [Equational Theories Project](https://teorth.github.io/equational_theories/):

$$
x = (y \star x) \star \bigl(x \star (z \star z)\bigr)
$$

for all $x, y, z$, written in ETP notation as `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.

* Orders 12, 14, and 15: no finite magma satisfies Equation 1486.
* Orders 17 and 26: explicit finite magmas satisfying Equation 1486 exist, verified directly by Lean's kernel without a SAT solver or external imports.

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
| Spectrum status | Combined with the ETP fork's proved bounds (no model at 2, 3, 5, 6, 7, 8, 10; model at all other orders outside `{12, 14, 15, 17, 26}`), the finite orders with no model of Equation 1486 are 2, 3, 5, 6, 7, 8, 10, 12, 14, and 15. The two developments are checked separately, not as one combined Lean theorem. |
| Prior art | Checked 22-24 November 2026: no earlier proof or model located for orders 12, 14, 15, 17, or 26 (bounded search, not a claim of absolute priority). Audits: [order 12](../PRIOR_ART.md#e1486-at-order-12), [order 14](../PRIOR_ART.md#e1486-at-order-14), [order 15](../PRIOR_ART.md#e1486-at-order-15), [order 17](../PRIOR_ART.md#e1486-at-order-17), [order 26](../PRIOR_ART.md#e1486-at-order-26). |

## Background and overview

A binary operation on $n$ elements is an $n\times n$ multiplication table whose entries are drawn from those same $n$ elements; the entry in row $a$, column $b$ is $a\star b$. No associativity or commutativity is assumed.

The [E1486 research notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md#remaining-small-orders) (revision `6a653268`) and live spectrum catalogue list orders 12, 14, 15, 17, and 26 as the five unresolved finite orders for Equation 1486 and its dual Equation 2126. This directory settles all five:

* [Order 15 exclusion](#order-15-no-model-with-15-elements) (counting bounds + 36 graph-family SAT refutations)
* [Order 12 exclusion](#no-model-with-12-elements) (49 square patterns, 48 SAT refutations)
* [Order 14 exclusion](#no-model-with-14-elements) (64 square patterns with lexicographic leader swaps, 63 SAT refutations)
* [Order 17 model](#a-model-with-17-elements) (explicit $17\times 17$ table, kernel-verified)
* [Order 26 model](#a-model-with-26-elements) (explicit $26\times 26$ table, kernel-verified)

Write $x^2 = x\star x$, so a "square" is simply a value on the table's diagonal, and let $Q$ be the set of distinct squares.

## Order 15: no model with 15 elements

**Theorem (`E1486.Simple.noTable`).** No binary operation on 15 elements satisfies $(y\star x)\star(x\star(z\star z))=x$ for all $x,y,z$.

A counting argument reduces the problem to 36 families of directed graphs. Lean then checks a SAT certificate ruling out every graph in each family.

### Three equalities

Fix a square $q=t^2$, choose any $x$, and put $u=x\star q$. The law gives

$$
x^2\star u=x,\qquad u\star q^2=q,\qquad u^2\star q=u.
$$

The first two equalities come from substituting $(x,y,z)=(x,x,t)$ and $(x,y,z)=(q,x,t)$ into the law. Substituting $(x,y,z)=(u,u,q)$ gives $u^2\star(u\star q^2)=u$; the second equality then gives the third.

**There are at least four squares.** For this one fixed $q$, the pair $(x^2,u^2)$ determines $x$. Its second entry recovers $u=u^2\star q$, and its first entry then recovers $x=x^2\star u$. If $k=|Q|$, 15 different elements therefore require $15\le k^2$.

### Replace the table by arrows

Draw $a\to a\star q$ for each square $q$. Also draw $b^2\to b$ for every $b$. If the same arrow arises more than once, count it only once. A two-step route has the form $a\to i\to b$. Vertices may repeat.

1. **There is at most one middle vertex on a two-step route between any given endpoints.** First observe that every arrow $a\to i$ gives $a=t\star i$ for some $t$. Take $t=a^2$ if $i=a\star q$, using the first equality above, and take $t=i$ if $a=i^2$. Now fix the endpoint $b$ and consider two cases.

   **Case 1: $b=v\star r$ for some vertex $v$ and square $r$.** The third equality gives $b^2\star r=b$. Thus the added arrow $b^2\to b$ is also obtained by multiplication by a square. Every last arrow $i\to b$ can therefore be written as $b=i\star q$ for some square $q$. Since $a=t\star i$, the defining law gives

   $$
   a\star b=(t\star i)\star(i\star q)=i.
   $$

   So the endpoints $a,b$ determine the middle vertex.

   **Case 2: no such $v,r$ exist.** The only arrow into $b$ is the added arrow $b^2\to b$. Any two-step route ending at $b$ must therefore have middle vertex $b^2$.

2. **Every vertex reaches every square in two steps.** The route is $a\to a\star q\to q$ by the second equality above.

3. **Every vertex has a square pointing to it.** This is the arrow $b^2\to b$.

The squares can be recognized from the arrows alone. Every square reaches itself in two steps by rule 2. Conversely, on a route $b\to i\to b$, the proof of rule 1 gives $i=b^2$ in both cases. Reading the same route as $i\to b\to i$ gives $b=i^2$. Thus $b$ is a square.

### Why there are at most eleven squares

Suppose there are $k\ge 12$ squares. Let $d$ and $D$ be the smallest and largest numbers of arrows leaving a vertex.

We have $d\le 3$. Otherwise, starting at any vertex would give at least $4\cdot 4=16$ two-step routes, all with different endpoints by rule 1. Also $D\ge 4$, since $3\cdot 3=9$ endpoints would be too few to reach all the squares.

Fix a square $q$. Count the three-step routes from $x$ to $q$ by their first arrow. Every neighbor of $x$ has exactly one two-step route to $q$, so the count equals the number of arrows leaving $x$. Counting by the last arrow instead, the same number is the number of predecessors of $q$ reachable from $x$ in two steps (where a predecessor is a vertex with an arrow into $q$). Consequently $q$ has at least $D$ predecessors.

Now fix a starting vertex of degree $d$. Exactly $d$ predecessors of each square are reached in two steps, so at least $D-d$ are missed. Every missed vertex is a nonsquare by rule 2. Counting arrows from missed vertices into squares gives at least $k(D-d)$ arrows. There are at most $15-k$ missed vertices, each with at most $D$ outgoing arrows, so

$$
k(D-d)\le(15-k)D.
$$

Since $k\ge 12$ and $d\le 3$, we get $12(D-3)\le 3D$, or $D\le 4$. Now $D=4$ forces $d=3$ and $k=12$. The inequality is an equality. Each of the three nonsquares must therefore send four arrows to squares. Each square must have exactly one missed predecessor in addition to the three reached, hence exactly four predecessors in total.

Take any nonsquare $u$ and any square $q$ it points to. There must be four three-step routes from $u$ to $q$, one for each arrow leaving $u$. But $u$ is one of the four predecessors of $q$, and $u$ cannot reach itself in two steps. This leaves at most three possible last arrows, a contradiction.

### The remaining finite check at order 15

We have proved $4\le k\le 11$. Taking $x=q$ in the second equality gives $(q^2)^2=q$. Thus the $k$ squares split into $j$ fixed points and $(k-j)/2$ pairs exchanged by squaring. For instance, four squares allow zero, two, or four fixed points. Counting the possibilities for $k=4,5,\ldots,11$ gives $3+3+4+4+5+5+6+6=36$ cases.

Each case fixes only the numbers $k,j$, leaving a whole family of possible graphs. There are 225 possible arrows, including loops. The 36 cases become 36 SAT instances: finite problems asking whether any choice of arrows satisfies all the constraints.

In each case, let $A$ be the $15\times 15$ zero-one matrix of arrows. Ordinary matrix multiplication makes $B_{ab}=(A^2)_{ab}$ the number of two-step routes from $a$ to $b$. Lean proves that no $A$ meets all four requirements below:

* Every entry of $B$ is at most one.
* Exactly the designated squares have $B_{qq}=1$. For each such $q$ the unique closed two-step route is $q\to q^2\to q$, using the partner specified by the case.
* For each such $q$, every entry of column $q$ of $B$ equals one.
* Every column of $A$ has a one in at least one square's row.

Relabeling vertices saves time without changing whether a graph satisfies the rules. Label the squares first, putting fixed points before exchanged pairs. Among labelings that preserve this pattern, choose one whose square-to-square adjacency entries, read row by row as a string of zeros and ones, are largest in dictionary order ($1>0$). Such a choice exists because there are finitely many labelings. Then sort the nonsquares in decreasing order of their arrow patterns: first their incoming arrows from squares, then their outgoing arrows to squares. This sorting leaves the square-to-square entries unchanged.

The finite test imposes ordering conditions satisfied by this choice. Every hypothetical graph can be relabeled this way, so the conditions cannot discard a counterexample. Lean proves this step before applying the finite checks.

For each case, Lean's `bv_decide` tactic obtains a refutation from the bundled SAT solver and checks it with a verified proof checker. The checker runs by native evaluation, so Lean's compiler and runtime are part of the trusted computation. Together, the 36 checked refutations rule out every possible table.

## No model with 12 elements

**Theorem (`E1486.Order12.noTable`).** No binary operation on 12 elements satisfies Equation 1486.

The three arrow rules hold for a table of any size, so a 12-element table would give a graph on 12 vertices that obeys them. Squaring exchanges the squares in pairs or fixes them, since $(q^2)^2=q$ as shown above. So label the squares first: there are $k$ of them, squaring fixes the first $j$, and it exchanges the rest in consecutive pairs. Since $k-j$ is even, there are 49 patterns $(k,j)$ with $0\le j\le k\le 12$.

This size needs neither the counting arguments nor the ordering conditions. For each pattern, Lean proves that no graph on 12 vertices meets all four requirements below:

* Some square points to each vertex.
* Each square $q$ has exactly one closed two-step route, the route $q\to q^2\to q$ through the partner the pattern assigns. A nonsquare has none.
* Every vertex reaches every square in two steps.
* Two different vertices never share both a predecessor and a successor. Otherwise two routes would join the same endpoints.

The pattern with no squares fails the first requirement outright. The other 48 are SAT refutations, checked as before.

The proof is in four short files: [Simple/Test.lean](Simple/Test.lean) states the four requirements for a graph on any number of vertices; [Simple/TestOfLaw.lean](Simple/TestOfLaw.lean) shows that the arrows of a relabeled table meet them; [Simple/Order12/Cases.lean](Simple/Order12/Cases.lean) refutes the 49 patterns; [Simple/Order12/NoTable.lean](Simple/Order12/NoTable.lean) combines them into `E1486.Order12.noTable`. Two ingredients are shared with order 15 and hold for tables of any size: [Simple/Graph.lean](Simple/Graph.lean) proves the arrow rules, and [Normalize.lean](Normalize.lean) proves that the squares can be labeled in this way.

**Prior-art status (23 November 2026):** no earlier exclusion of order 12 was located, and no 12-element model. The research notes and live spectrum data list 12 as unresolved; their recorded solver runs stopped at 60 or 900 seconds (apart from one restricted family), and a Mace4 run reported on the Lean Zulip was stopped after 14 hours. See the [audit](../PRIOR_ART.md#e1486-at-order-12).

## No model with 14 elements

**Theorem (`E1486.Order14.noTable`).** No binary operation on 14 elements satisfies Equation 1486.

A 14-element table would give a graph on 14 vertices that meets the same four requirements, with one of the 64 patterns $(k,j)$ for $0\le j\le k\le 14$. At this size the requirements alone are too much for the solver: in a trial, 27 of the 63 patterns with a square were still undecided after a minute each. The same graph can be labeled in many ways, so the labels are pinned down further.

Read a fixed list of arrows as a string of zeros and ones: first the arrows among the squares, row by row, then for each nonsquare in turn its arrows from the squares and its arrows to the squares. Among the tables that satisfy the law with the squares first in the same pattern, choose one whose string is largest in dictionary order. There are finitely many strings, so one exists. Relabeling it in a way that keeps the pattern gives another such table, so the string cannot become larger. The test asks this of four kinds of swap:

* two consecutive squares fixed by squaring;
* the two squares of an exchanged pair;
* two consecutive pairs;
* two consecutive nonsquares.

Each swap keeps the squares first and commutes with squaring on the squares, so it keeps the pattern. A pattern has at most 13 such swaps. These conditions are fewer than the ordering conditions of the order-15 proof, and each one compares the whole string, which shortens the argument that some table meets them. Lean proves that argument for tables of any size.

The pattern with no squares fails the first requirement outright. With the ordering conditions added, the other 63 are SAT refutations, checked as before.

The test and the proof that a relabeled table passes it are the two files shared with order 12. [Simple/Leader.lean](Simple/Leader.lean) states the ordering conditions; [Simple/LeaderOfLaw.lean](Simple/LeaderOfLaw.lean) proves that if a table satisfies the law, then so does one that meets them; [Simple/Order14/Cases.lean](Simple/Order14/Cases.lean) refutes the 64 patterns; and [Simple/Order14/NoTable.lean](Simple/Order14/NoTable.lean) combines these into `E1486.Order14.noTable`.

**Prior-art status (24 November 2026):** no earlier exclusion of order 14 was located, and no 14-element model. The research notes and live spectrum data list 14 as unresolved; their one recorded attempt is a solver run stopped after 60 seconds. See the [audit](../PRIOR_ART.md#e1486-at-order-14).

## A model with 17 elements

Order 17 goes the other way: some binary operation on 17 elements satisfies Equation 1486. [Simple/Order17.lean](Simple/Order17.lean) lists its $17\times 17$ table, and Lean checks all $17^3 = 4,913$ instances of the law directly. This check uses no SAT certificate and no native evaluation, and the file imports nothing (`E1486.Order17.exists_table`, depending only on `propext`).

**Prior-art status (23 November 2026):** no earlier 17-element model was located. The research notes and live spectrum data list 17 as unresolved; their one recorded attempt is a solver run stopped after 60 seconds. See the [audit](../PRIOR_ART.md#e1486-at-order-17).

## A model with 26 elements

Order 26 also has a model. [Simple/Order26.lean](Simple/Order26.lean) lists its $26\times 26$ table, and Lean checks all $26^3 = 17,576$ instances of the law directly, again with no SAT certificate, no native evaluation, and no imports (`E1486.Order26.exists_table`, depending only on `propext`). The table has six squares, two of them fixed by squaring.

The table came from the graph test above, run for 26 vertices with that pattern of squares. A satisfying graph gives a table: $a\star b$ is the middle vertex of the two-step route from $a$ to $b$ when there is one, and otherwise any square with an arrow to $b$.

**Prior-art status (24 November 2026):** no earlier 26-element model was located, and no exclusion of order 26. The research notes and live spectrum data list 26 as unresolved. The notes record three restricted searches for a 26-element model, each refuted, and one unrestricted solver run stopped after 60 seconds. See the [audit](../PRIOR_ART.md#e1486-at-order-26).

## Reproduce

The source bundle builds with the pinned Lean 4.36.0 toolchain and its bundled SAT solver. From this directory run:

```sh
# Order 15 exclusion (36 SAT/LRAT refutations)
lake build +Simple.NoTable

# Order 12 exclusion (48 SAT/LRAT refutations; ~6–8 minutes on desktop)
lake build Simple.Order12.NoTable

# Order 14 exclusion (63 SAT/LRAT refutations; ~13 minutes on desktop)
lake build Simple.Order14.NoTable

# Order 17 model (kernel check, a few seconds)
lake build Simple.Order17

# Order 26 model (kernel check, a few seconds)
lake build Simple.Order26
```

A plain `lake build` checks everything in this directory: all five settled orders plus [Simple/AdditionalResults.lean](Simple/AdditionalResults.lean) (which collects related results not needed for the main proofs: converse graph constructions, extra square-row lemmas, and the older symmetry argument).

To inspect the axioms of any endpoint:

```sh
printf '%s\n' 'import Simple.NoTable' '#print axioms E1486.Simple.noTable' | lake env lean --stdin
printf '%s\n' 'import Simple.Order12.NoTable' '#print axioms E1486.Order12.noTable' | lake env lean --stdin
printf '%s\n' 'import Simple.Order14.NoTable' '#print axioms E1486.Order14.noTable' | lake env lean --stdin
printf '%s\n' 'import Simple.Order17' '#print axioms E1486.Order17.exists_table' | lake env lean --stdin
printf '%s\n' 'import Simple.Order26' '#print axioms E1486.Order26.exists_table' | lake env lean --stdin
```

The three exclusions depend on Lean's standard logical axioms plus the native-evaluation axioms of their SAT/LRAT checks (36, 48, and 63 checks respectively); there are no admitted lemmas. The order-17 and order-26 models depend only on `propext`.

To follow the formal argument for order 15, start with [Simple/NoTable.lean](Simple/NoTable.lean). It combines the graph reduction, the two counting bounds, and the finite exclusions. The three equalities are named `recover_source`, `return_to_square`, and `recover_target` in [E1486.lean](E1486.lean); [Simple/Graph.lean](Simple/Graph.lean) uses them to prove the arrow rules; [Simple/FiniteBase.lean](Simple/FiniteBase.lean) explains how each graph condition is encoded.

### Independent Python + CaDiCaL check

An independent Python implementation of the graph test is included as [Simple/check.py](Simple/check.py). It needs Python 3 and CaDiCaL (found on `PATH` or in the pinned Lean installation):

```sh
python3 Simple/check.py 15
python3 Simple/check.py 12
python3 Simple/check.py 14
python3 Simple/check.py 17
python3 Simple/check.py --pattern 6:2 26
```

Expected summaries:

* `order 15: 71 cases, all UNSAT` (all 71 patterns for $1\le k\le 15$; Lean eliminates $k\le 3$ and $k\ge 12$ by counting, leaving 36).
* `order 12: 48 cases, all UNSAT` (within seconds; Python imposes ordering conditions that Lean omits at order 12).
* `order 14: 63 cases, all UNSAT` (~20 seconds; Python imposes the order-15 ordering conditions rather than Lean's shorter swap list).
* `order 17: model verified on all 4913 triples (k=6, j=4)` (~1 minute; differs from the Lean model, which has 8 squares).
* `order 26: model verified on all 17576 triples (k=6, j=2)` (under 1 minute; without `--pattern 6:2`, pattern `6:0` did not finish within 10 minutes).

To also replay every order-15 refutation with a separate certificate checker, use `lrat-trim` **0.2.1-rc3**, pinned to [revision `423194927df747528d5b7364806b5b77b2660c12`](https://github.com/arminbiere/lrat-trim/tree/423194927df747528d5b7364806b5b77b2660c12) (which supports `--rup`, unlike 0.2.0):

```sh
python3 Simple/check.py --verify-with /path/to/lrat-trim 15
```

This reports `order 15: 71 cases, all RUP proofs verified`.

## Attribution and license

The square-row identity used in the reduction also appears in the [Equational Theories Project's E1486 notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md). This directory retains its [Apache-2.0 license](LICENSE) and the copyright notice of the Equational Theories Project contributors.
