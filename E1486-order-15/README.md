# Equation 1486 finite magma spectrum (orders 12, 14, 15, 17, and 26)

Lean 4 proofs settling the five unresolved finite orders (12, 14, 15, 17, and 26) for Equation 1486 (`E1486`, dual Equation 2126) of the [Equational Theories Project](https://teorth.github.io/equational_theories/):

$$
x = (y \star x) \star \bigl(x \star (z \star z)\bigr)
$$

for all $x, y, z$, written in ETP notation as `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.

* Orders 12, 14, and 15: no finite magma satisfies Equation 1486.
* Orders 17 and 26: explicit finite magmas satisfy Equation 1486, verified directly by Lean's kernel with no SAT solver or external imports.

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
| Prior art | Checked 22-24 November 2026: no earlier proof or model was found for orders 12, 14, 15, 17, or 26 (bounded search, not a claim of absolute priority). Audits: [order 12](../PRIOR_ART.md#e1486-at-order-12), [order 14](../PRIOR_ART.md#e1486-at-order-14), [order 15](../PRIOR_ART.md#e1486-at-order-15), [order 17](../PRIOR_ART.md#e1486-at-order-17), [order 26](../PRIOR_ART.md#e1486-at-order-26). |

## Background and overview

A binary operation on $n$ elements is an $n\times n$ multiplication table whose entries come from those same $n$ elements. The entry in row $a$, column $b$ is $a\star b$, with no associativity or commutativity assumed.

The [E1486 research notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md#remaining-small-orders) (revision `6a653268`) and live spectrum catalogue list orders 12, 14, 15, 17, and 26 as the five unresolved finite orders for Equation 1486 and its dual Equation 2126. This directory settles all five:

* [Order 15 exclusion](#order-15-no-model-with-15-elements) (counting bounds + 36 graph-family SAT refutations)
* [Order 12 exclusion](#no-model-with-12-elements) (49 square patterns, 48 SAT refutations)
* [Order 14 exclusion](#no-model-with-14-elements) (64 square patterns with lexicographic leader swaps, 63 SAT refutations)
* [Order 17 model](#a-model-with-17-elements) (explicit $17\times 17$ table, kernel-verified)
* [Order 26 model](#a-model-with-26-elements) (explicit $26\times 26$ table, kernel-verified)

Write $x^2 = x\star x$, so a "square" is a value on the table's diagonal, and let $Q$ be the set of distinct squares.

## Order 15: no model with 15 elements

The theorem `E1486.Simple.noTable` proves that no binary operation on 15 elements satisfies $(y\star x)\star(x\star(z\star z))=x$ for all $x,y,z$.

A counting argument reduces the problem to 36 families of directed graphs. Lean then checks a SAT certificate ruling out every graph in each family.

### Three equalities

Fix a square $q=t^2$, pick any $x$, and set $u=x\star q$. The law gives

$$
x^2\star u=x,\qquad u\star q^2=q,\qquad u^2\star q=u.
$$

The first two equalities come from substituting $(x,y,z)=(x,x,t)$ and $(x,y,z)=(q,x,t)$ into the law. Substituting $(x,y,z)=(u,u,q)$ gives $u^2\star(u\star q^2)=u$, and the second equality turns that into the third.

This already shows there are at least four squares. For a fixed square $q$, the pair $(x^2,u^2)$ determines $x$: its second entry recovers $u=u^2\star q$, and its first entry then recovers $x=x^2\star u$. If $k=|Q|$, then 15 distinct elements require $15\le k^2$.

### Replace the table by arrows

Draw $a\to a\star q$ for each square $q$, and also draw $b^2\to b$ for every $b$. Count duplicate arrows only once. A two-step route has the form $a\to i\to b$, with repeated vertices allowed.

These arrows obey three rules:

1. There is at most one middle vertex on a two-step route between any two endpoints.

   First, every arrow $a\to i$ gives $a=t\star i$ for some $t$: take $t=a^2$ if $i=a\star q$ (by the first equality), and take $t=i$ if $a=i^2$. Now fix $b$.

   If $b=v\star r$ for some vertex $v$ and square $r$, the third equality gives $b^2\star r=b$. So the added arrow $b^2\to b$ also comes from multiplying by a square. Every last arrow $i\to b$ therefore has the form $b=i\star q$ for some square $q$. Since $a=t\star i$, the defining law gives

   $$
   a\star b=(t\star i)\star(i\star q)=i,
   $$

   so $a$ and $b$ determine the middle vertex $i$.

   If no such $v,r$ exist, the only arrow into $b$ is $b^2\to b$. Every two-step route ending at $b$ must then pass through $b^2$.

2. Every vertex reaches every square in two steps, via $a\to a\star q\to q$ (by the second equality).

3. Every vertex has a square pointing to it, namely $b^2\to b$.

The squares can be identified from the arrows alone. Every square reaches itself in two steps by rule 2. Conversely, on a route $b\to i\to b$, the proof of rule 1 gives $i=b^2$ in both cases. Reading the same route as $i\to b\to i$ gives $b=i^2$, so $b$ is a square.

### Why there are at most eleven squares

Suppose there are $k\ge 12$ squares. Let $d$ and $D$ be the smallest and largest numbers of arrows leaving a vertex.

We must have $d\le 3$, because otherwise any starting vertex would have at least $4\cdot 4=16$ two-step routes with distinct endpoints (by rule 1). We also need $D\ge 4$, since $3\cdot 3=9$ endpoints cannot reach 12 squares.

Fix a square $q$. Count the three-step routes from $x$ to $q$ by their first arrow. Every neighbor of $x$ has a unique two-step route to $q$, so the count equals the out-degree of $x$. Counting by the last arrow instead gives the number of predecessors of $q$ reachable from $x$ in two steps (where a predecessor is a vertex with an arrow into $q$). So $q$ has at least $D$ predecessors.

Now pick a starting vertex of degree $d$. Exactly $d$ predecessors of each square are reached in two steps, leaving at least $D-d$ missed. Every missed vertex is a nonsquare by rule 2. Counting arrows from missed vertices into squares gives at least $k(D-d)$ arrows. There are at most $15-k$ missed vertices, each with at most $D$ outgoing arrows, so

$$
k(D-d)\le(15-k)D.
$$

With $k\ge 12$ and $d\le 3$, this gives $12(D-3)\le 3D$, so $D\le 4$. Then $D=4$ forces $d=3$ and $k=12$, and the inequality must be an equality. Each of the three nonsquares therefore sends four arrows to squares, and each square has exactly one missed predecessor in addition to the three reached, making four predecessors in all.

Pick any nonsquare $u$ and any square $q$ it points to. There must be four three-step routes from $u$ to $q$, one for each arrow leaving $u$. But $u$ is one of the four predecessors of $q$, and $u$ cannot reach itself in two steps. That leaves at most three possible last arrows, a contradiction.

### The remaining finite check at order 15

We now have $4\le k\le 11$. Taking $x=q$ in the second equality gives $(q^2)^2=q$, so squaring splits the $k$ squares into $j$ fixed points and $(k-j)/2$ swapped pairs. For example, four squares allow zero, two, or four fixed points. Summing over $k=4,5,\ldots,11$ gives $3+3+4+4+5+5+6+6=36$ cases.

Each case fixes only $k$ and $j$, leaving a family of candidate graphs on 225 possible arrows (including loops). The 36 cases become 36 SAT instances asking whether any choice of arrows meets all constraints.

In each case, let $A$ be the $15\times 15$ zero-one adjacency matrix, so $B_{ab}=(A^2)_{ab}$ counts two-step routes from $a$ to $b$. Lean proves that no $A$ meets all four conditions:

* Every entry of $B$ is at most 1.
* Exactly the designated squares have $B_{qq}=1$, and for each such $q$ the unique closed two-step route is $q\to q^2\to q$ using the partner fixed by the case.
* For each such $q$, every entry in column $q$ of $B$ equals 1.
* Every column of $A$ has a 1 in at least one square's row.

Relabeling vertices speeds up the solver without changing validity. Put the squares first, with fixed points before swapped pairs. Among all labelings preserving this pattern, pick one whose square-to-square adjacency entries (read row by row as a bitstring) are largest in dictionary order ($1>0$). Such a labeling exists because there are finitely many labelings. Then sort the nonsquares in decreasing order of their arrow patterns: first incoming arrows from squares, then outgoing arrows to squares. This leaves the square-to-square entries intact.

The finite check adds ordering constraints satisfied by this canonical choice. Since every hypothetical graph can be relabeled this way, the constraints cannot discard a counterexample. Lean proves this reduction before running the finite checks.

For each case, Lean's `bv_decide` tactic gets a refutation from the bundled SAT solver and checks it with a verified proof checker. The checker runs via native evaluation, so Lean's compiler and runtime are inside the trust boundary. Together, the 36 checked refutations rule out every 15-element table.

## No model with 12 elements

The theorem `E1486.Order12.noTable` proves that no binary operation on 12 elements satisfies Equation 1486.

The three arrow rules hold at any size, so a 12-element table would give a 12-vertex graph obeying them. Because $(q^2)^2=q$, squaring fixes some squares and swaps the rest in pairs. Put the $k$ squares first, with $j$ fixed points followed by $(k-j)/2$ consecutive swapped pairs. Since $k-j$ is even, there are 49 patterns $(k,j)$ with $0\le j\le k\le 12$.

At order 12 we need neither the counting bounds nor the ordering constraints. For each pattern, Lean proves no 12-vertex graph satisfies all four conditions:

* Some square points to each vertex.
* Each square $q$ has a unique closed two-step route, $q\to q^2\to q$, through its assigned partner. Nonsquares have none.
* Every vertex reaches every square in two steps.
* No two distinct vertices share both a predecessor and a successor (which would create two routes with the same endpoints).

The pattern with no squares fails the first condition right away. The other 48 are refuted by SAT certificates checked as before.

The proof spans four short files: [Simple/Test.lean](Simple/Test.lean) states the four graph conditions for any size; [Simple/TestOfLaw.lean](Simple/TestOfLaw.lean) shows that arrows from a relabeled table satisfy them; [Simple/Order12/Cases.lean](Simple/Order12/Cases.lean) refutes the 49 patterns; and [Simple/Order12/NoTable.lean](Simple/Order12/NoTable.lean) combines them into `E1486.Order12.noTable`. Two shared files hold for any size: [Simple/Graph.lean](Simple/Graph.lean) proves the arrow rules, and [Normalize.lean](Normalize.lean) puts the squares in standard order.

Prior art (checked 23 November 2026): no earlier exclusion or model at order 12 was found. The research notes and live spectrum data list 12 as unresolved; their recorded solver runs stopped at 60 or 900 seconds (apart from one restricted family), and a Mace4 run reported on the Lean Zulip stopped after 14 hours. See the [audit](../PRIOR_ART.md#e1486-at-order-12).

## No model with 14 elements

The theorem `E1486.Order14.noTable` proves that no binary operation on 14 elements satisfies Equation 1486.

A 14-element table would give a 14-vertex graph meeting the same four conditions under one of the 64 patterns $(k,j)$ with $0\le j\le k\le 14$. At this size the conditions alone are too slow for the solver: in a trial, 27 of the 63 patterns with a square were still undecided after a minute each. To break symmetry, we pin down the labeling further.

Read a fixed list of arrows as a bitstring: first the arrows among the squares row by row, then for each nonsquare its incoming arrows from squares and its outgoing arrows to squares. Among all valid tables with the squares first in that pattern, choose one whose bitstring is largest in dictionary order. Because there are finitely many strings, one exists. Any relabeling that keeps the pattern gives another valid table, so it cannot increase the string. The test enforces this for four kinds of swaps:

* two consecutive squares fixed by squaring;
* the two squares of a swapped pair;
* two consecutive pairs;
* two consecutive nonsquares.

Each swap keeps the squares first and commutes with squaring on the squares, so it preserves the pattern. A pattern has at most 13 such swaps. That is fewer conditions than in the order-15 proof, and comparing the whole string simplifies the proof that a maximal labeling exists. Lean proves that lemma for tables of any size.

The pattern with no squares fails the first condition outright. With the swap conditions added, the other 63 patterns are refuted by SAT certificates checked as before.

The graph test and its proof from the law come from the same two files used at order 12. [Simple/Leader.lean](Simple/Leader.lean) states the swap conditions, [Simple/LeaderOfLaw.lean](Simple/LeaderOfLaw.lean) proves that every valid table can be relabeled to meet them, [Simple/Order14/Cases.lean](Simple/Order14/Cases.lean) refutes the 64 patterns, and [Simple/Order14/NoTable.lean](Simple/Order14/NoTable.lean) proves `E1486.Order14.noTable`.

Prior art (checked 24 November 2026): no earlier exclusion or model at order 14 was found. The research notes and live spectrum data list 14 as unresolved, recording only one solver run stopped after 60 seconds. See the [audit](../PRIOR_ART.md#e1486-at-order-14).

## A model with 17 elements

Order 17 goes the other way: a 17-element binary operation satisfies Equation 1486. [Simple/Order17.lean](Simple/Order17.lean) gives its $17\times 17$ table, and Lean checks all $17^3 = 4,913$ instances of the law directly. This check uses no SAT certificate, no native evaluation, and no imports (`E1486.Order17.exists_table`, depending only on `propext`).

Prior art (checked 23 November 2026): no earlier 17-element model was found. The research notes and live spectrum data list 17 as unresolved, recording only one solver run stopped after 60 seconds. See the [audit](../PRIOR_ART.md#e1486-at-order-17).

## A model with 26 elements

Order 26 also has a model. [Simple/Order26.lean](Simple/Order26.lean) gives its $26\times 26$ table, and Lean checks all $26^3 = 17,576$ instances of the law directly, again with no SAT certificate, no native evaluation, and no imports (`E1486.Order26.exists_table`, depending only on `propext`). The table has six squares, two of them fixed by squaring.

The table came from running the graph test above on 26 vertices with that square pattern. Any satisfying graph gives a table: set $a\star b$ to the middle vertex of the two-step route from $a$ to $b$ when one exists, and otherwise to any square with an arrow to $b$.

Prior art (checked 24 November 2026): no earlier 26-element model or exclusion was found. The research notes and live spectrum data list 26 as unresolved, recording three restricted searches (each refuted) and one unrestricted solver run stopped after 60 seconds. See the [audit](../PRIOR_ART.md#e1486-at-order-26).

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

A plain `lake build` checks everything in this directory: all five settled orders plus [Simple/AdditionalResults.lean](Simple/AdditionalResults.lean) (extra results not needed for the main proofs: converse graph constructions, extra square-row lemmas, and the older symmetry argument).

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

### Independent Python + CaDiCaL check

An independent Python implementation of the graph test lives in [Simple/check.py](Simple/check.py). It needs Python 3 and CaDiCaL (on `PATH` or inside the pinned Lean installation):

```sh
python3 Simple/check.py 15
python3 Simple/check.py 12
python3 Simple/check.py 14
python3 Simple/check.py 17
python3 Simple/check.py --pattern 6:2 26
```

Expected summaries:

* `order 15: 71 cases, all UNSAT` (all 71 patterns for $1\le k\le 15$; Lean eliminates $k\le 3$ and $k\ge 12$ by counting, leaving 36).
* `order 12: 48 cases, all UNSAT` (takes seconds; Python adds ordering conditions that Lean omits at order 12).
* `order 14: 63 cases, all UNSAT` (~20 seconds; Python uses the order-15 ordering conditions rather than Lean's shorter swap list).
* `order 17: model verified on all 4913 triples (k=6, j=4)` (~1 minute; differs from the Lean model, which has 8 squares).
* `order 26: model verified on all 17576 triples (k=6, j=2)` (under 1 minute; without `--pattern 6:2`, pattern `6:0` did not finish within 10 minutes).

To replay every order-15 refutation with an external certificate checker, use `lrat-trim` **0.2.1-rc3**, pinned to [revision `423194927df747528d5b7364806b5b77b2660c12`](https://github.com/arminbiere/lrat-trim/tree/423194927df747528d5b7364806b5b77b2660c12) (which supports `--rup`, unlike 0.2.0):

```sh
python3 Simple/check.py --verify-with /path/to/lrat-trim 15
```

This reports `order 15: 71 cases, all RUP proofs verified`.

## Attribution and license

The square-row identity used in the reduction also appears in the [Equational Theories Project's E1486 notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md). This directory keeps its [Apache-2.0 license](LICENSE) and the copyright notice of the Equational Theories Project contributors.
