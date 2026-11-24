# E1486 order 15: a Lean proof of finite magma nonexistence

**Prior-art status (22 November 2026):** no earlier proof of this exact
order-15 exclusion was located. The inspected public spectrum catalogue
still lists 15 as open. This is a bounded search finding, not a claim of
absolute priority. See the [audit and live-source evidence](../PRIOR_ART.md#e1486-at-order-15).
Related identifiers include *Equation 1486*, *magma spectrum*, and the dual
law *E2126*.

**Theorem.** No binary operation on 15 elements satisfies
$$
(y\star x)\star\bigl(x\star(z\star z)\bigr)=x
$$
for all $x,y,z$.

A binary operation on 15 elements is a $15\times15$ table whose entries are drawn from those same 15 elements. The entry in row $a$, column $b$ is $a\star b$. We assume no associativity or commutativity.

The [E1486 research notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md#remaining-small-orders), at revision `6a653268`, list orders 12, 14, 15, 17, and 26 as unresolved. This computer-assisted proof settles the 15-element case. The same arrow rules [rule out order 12](#no-model-with-12-elements). A [17-element model](#a-model-with-17-elements) settles order 17, and a [26-element model](#a-model-with-26-elements) settles order 26. Of the listed orders, only 14 remains.

Write $x^2=x\star x$, so a "square" is simply a value on the table's diagonal. Let $Q$ be the set of distinct squares. A counting argument reduces the problem to 36 families of graphs. Lean then checks a certificate ruling out every graph in each family. The argument below explains the reduction; the final exclusions depend on that computation.

## Three equalities

Fix a square $q=t^2$, choose any $x$, and put $u=x\star q$. The law gives
$$
x^2\star u=x,\qquad u\star q^2=q,\qquad u^2\star q=u.
$$
The first two equalities come from substituting $(x,y,z)=(x,x,t)$ and $(x,y,z)=(q,x,t)$ into the law. Substituting $(x,y,z)=(u,u,q)$ gives $u^2\star(u\star q^2)=u$; the second equality then gives the third.

**There are at least four squares.** For this one fixed $q$, the pair $(x^2,u^2)$ determines $x$. Its second entry recovers $u=u^2\star q$, and its first entry then recovers $x=x^2\star u$. If $k=|Q|$, 15 different elements therefore require $15\le k^2$.

## Replace the table by arrows

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

## Why there are at most eleven squares

Suppose there are $k\ge12$ squares. Let $d$ and $D$ be the smallest and largest numbers of arrows leaving a vertex.

We have $d\le3$. Otherwise, starting at any vertex would give at least $4\cdot4=16$ two-step routes, all with different endpoints by rule 1. Also $D\ge4$, since $3\cdot3=9$ endpoints would be too few to reach all the squares.

Fix a square $q$. Count the three-step routes from $x$ to $q$ by their first arrow. Every neighbor of $x$ has exactly one two-step route to $q$, so the count equals the number of arrows leaving $x$. Counting by the last arrow instead, the same number is the number of predecessors of $q$ reachable from $x$ in two steps. Here a predecessor is a vertex with an arrow into $q$. Consequently $q$ has at least $D$ predecessors.

Now fix a starting vertex of degree $d$. Exactly $d$ predecessors of each square are reached in two steps, so at least $D-d$ are missed. Every missed vertex is a nonsquare by rule 2. Counting arrows from missed vertices into squares gives at least $k(D-d)$ arrows. There are at most $15-k$ missed vertices, each with at most $D$ outgoing arrows, so
$$
k(D-d)\le(15-k)D.
$$
Since $k\ge12$ and $d\le3$, we get $12(D-3)\le3D$, or $D\le4$. Now $D=4$ forces $d=3$ and $k=12$. The inequality is an equality. Each of the three nonsquares must therefore send four arrows to squares. Each square must have exactly one missed predecessor in addition to the three reached, hence exactly four predecessors in total.

Take any nonsquare $u$ and any square $q$ it points to. There must be four three-step routes from $u$ to $q$, one for each arrow leaving $u$. But $u$ is one of the four predecessors of $q$, and $u$ cannot reach itself in two steps. This leaves at most three possible last arrows, a contradiction.

## The remaining finite check

We have proved $4\le k\le11$. Taking $x=q$ in the second equality gives $(q^2)^2=q$. Thus the $k$ squares split into $j$ fixed points and $(k-j)/2$ pairs exchanged by squaring. For instance, four squares allow zero, two or four fixed points. Counting the possibilities for $k=4,5,\ldots,11$ gives $3+3+4+4+5+5+6+6=36$ cases.

Each case fixes only the numbers $k,j$, leaving a whole family of possible graphs. There are 225 possible arrows, including loops. The 36 cases become 36 SAT instances: finite problems asking whether any choice of arrows satisfies all the constraints.

In each case, let $A$ be the $15\times15$ zero-one matrix of arrows. Ordinary matrix multiplication makes $B_{ab}=(A^2)_{ab}$ the number of two-step routes from $a$ to $b$. Lean proves that no $A$ meets all four requirements below.

* Every entry of $B$ is at most one.
* Exactly the designated squares have $B_{qq}=1$. For each such $q$ the unique closed two-step route is $q\to q^2\to q$, using the partner specified by the case.
* For each such $q$, every entry of column $q$ of $B$ equals one.
* Every column of $A$ has a one in at least one square's row.

Relabeling vertices saves time without changing whether a graph satisfies the rules. Label the squares first, putting fixed points before exchanged pairs. Among labelings that preserve this pattern, choose one whose square-to-square adjacency entries, read row by row as a string of zeros and ones, are largest in dictionary order ($1>0$). Such a choice exists because there are finitely many labelings. Then sort the nonsquares in decreasing order of their arrow patterns: first their incoming arrows from squares, then their outgoing arrows to squares. This sorting leaves the square-to-square entries unchanged.

The finite test imposes ordering conditions satisfied by this choice. Every hypothetical graph can be relabeled this way, so the conditions cannot discard a counterexample. Lean proves this step before applying the finite checks.

For each case, Lean's `bv_decide` tactic obtains a refutation from the bundled SAT solver and checks it with a verified proof checker. The checker runs by native evaluation, so Lean's compiler and runtime are part of the trusted computation. Together, the 36 checked refutations rule out every possible table.

## No model with 12 elements

**Theorem.** No binary operation on 12 elements satisfies the law.

The three arrow rules hold for a table of any size, so a 12-element table would give a graph on 12 vertices that obeys them. Squaring exchanges the squares in pairs or fixes them, since $(q^2)^2=q$ as shown above. So label the squares first: there are $k$ of them, squaring fixes the first $j$, and it exchanges the rest in consecutive pairs. Since $k-j$ is even, there are 49 patterns $(k,j)$ with $0\le j\le k\le12$.

This size needs neither the counting arguments nor the ordering conditions. For each pattern, Lean proves that no graph on 12 vertices meets all four requirements below.

* Some square points to each vertex.
* Each square $q$ has exactly one closed two-step route, the route $q\to q^2\to q$ through the partner the pattern assigns. A nonsquare has none.
* Every vertex reaches every square in two steps.
* Two different vertices never share both a predecessor and a successor. Otherwise two routes would join the same endpoints.

The pattern with no squares fails the first requirement outright. The other 48 are SAT refutations, checked as before.

The proof is in four short files in [Simple/Order12](Simple/Order12). [Test.lean](Simple/Order12/Test.lean) states the four requirements. [Check.lean](Simple/Order12/Check.lean) shows that the arrows of a relabeled table meet them. [Cases.lean](Simple/Order12/Cases.lean) refutes the 49 patterns. [NoTable.lean](Simple/Order12/NoTable.lean) combines them into the theorem `E1486.Order12.noTable`. Two ingredients are shared with order 15 and hold for tables of any size: [Simple/Graph.lean](Simple/Graph.lean) proves the arrow rules, and [Normalize.lean](Normalize.lean) proves that the squares can be labeled in this way. The further ordering of labels used for order 15 is not needed here.

**Prior-art status (23 November 2026):** no earlier exclusion of order 12 was located, and no 12-element model. The research notes and the live spectrum data list 12 as unresolved. Their recorded solver runs at this order stopped at limits of 60 or 900 seconds, apart from one restricted family that was refuted. A Mace4 run reported on the Lean Zulip was stopped after 14 hours. See the [audit](../PRIOR_ART.md#e1486-at-order-12).

## A model with 17 elements

Order 17 goes the other way: some binary operation on 17 elements satisfies the law. [Simple/Order17.lean](Simple/Order17.lean) lists its $17\times17$ table, and Lean checks all $17^3=4913$ instances of the law directly. This check uses no SAT certificate and no native evaluation, and the file imports nothing.

**Prior-art status (23 November 2026):** no earlier 17-element model was located. The research notes and the live spectrum data list 17 as unresolved; their one recorded attempt at this order is a solver run stopped after 60 seconds. See the [audit](../PRIOR_ART.md#e1486-at-order-17).

## A model with 26 elements

Order 26 also has a model. [Simple/Order26.lean](Simple/Order26.lean) lists its $26\times26$ table, and Lean checks all $26^3=17576$ instances of the law directly, again with no SAT certificate, no native evaluation, and no imports. The table has six squares, two of them fixed by squaring.

The table came from the graph test above, run for 26 vertices with that pattern of squares. A satisfying graph gives a table: $a\star b$ is the middle vertex of the two-step route from $a$ to $b$ when there is one, and otherwise any square with an arrow to $b$.

**Prior-art status (24 November 2026):** no earlier 26-element model was located, and no exclusion of order 26. The research notes and the live spectrum data list 26 as unresolved. The notes record three restricted searches for a 26-element model, each refuted, and one unrestricted solver run stopped after 60 seconds. See the [audit](../PRIOR_ART.md#e1486-at-order-26).

## Reproduce

The source bundle builds with the pinned Lean 4.36.0 toolchain and its bundled SAT solver. From its top directory run

```sh
lake build +Simple.NoTable
```

The endpoint is `E1486.Simple.noTable`. The build generates and checks all 36 finite refutations locally. Its dependencies include the standard logical axioms and the native-evaluation axioms for those checks; there are no admitted lemmas. To inspect them, run

```sh
printf '%s\n' 'import Simple.NoTable' '#print axioms E1486.Simple.noTable' | lake env lean --stdin
```

The order-12 exclusion can be built on its own:

```sh
lake build Simple.Order12.NoTable
```

Its endpoint is `E1486.Order12.noTable`. On a desktop machine the build took six to eight minutes; the 48 SAT refutations run one after another, so more cores do not shorten it. The theorem depends on the standard logical axioms and on the native-evaluation axioms of those 48 refutations. To inspect them, run

```sh
printf '%s\n' 'import Simple.Order12.NoTable' '#print axioms E1486.Order12.noTable' | lake env lean --stdin
```

The order-17 model is checked separately, in a few seconds:

```sh
lake build Simple.Order17
```

Its endpoint is `E1486.Order17.exists_table`, which depends only on the axiom `propext`.

The order-26 model is checked the same way:

```sh
lake build Simple.Order26
```

Its endpoint is `E1486.Order26.exists_table`, which also depends only on `propext`.

To follow the formal argument for order 15, start with [Simple/NoTable.lean](Simple/NoTable.lean). It combines the graph reduction, the two counting bounds, and the finite exclusions. The three equalities are named `recover_source`, `return_to_square`, and `recover_target` in [E1486.lean](E1486.lean); [Simple/Graph.lean](Simple/Graph.lean) uses them to prove the arrow rules. [Simple/FiniteBase.lean](Simple/FiniteBase.lean) explains how each graph condition is encoded.

Related results that the proof does not need are collected in [Simple/AdditionalResults.lean](Simple/AdditionalResults.lean): the converse graph constructions, extra square-row lemmas, and the older symmetry argument. Their declaration names are preserved; import `Simple.AdditionalResults` to use them. A plain `lake build` checks everything in this directory: the order-15 proof, the order-12 exclusion, the order-17 and order-26 models, and this module.

An independent Python implementation of the graph test is included as `Simple/check.py`. It needs Python 3 and CaDiCaL, which it finds on `PATH` or in the pinned Lean installation. From the same directory run

```sh
python3 Simple/check.py 15
```

Expected output:

```text
order 15: 71 cases, all UNSAT
```

Here `UNSAT` means no graph satisfies the constraints. The Python program checks all 71 fixed-point/pair patterns for $1\le k\le15$. Lean uses the counting arguments to eliminate $k\le3$ and $k\ge12$, leaving 36 patterns to check computationally.

For order 12, `python3 Simple/check.py 12` prints `order 12: 48 cases, all UNSAT` within seconds. These are the 48 patterns with $1\le k\le12$. The Python program also imposes the ordering conditions; Lean does not need them at this size.

The same program finds a 17-element model independently:

```sh
python3 Simple/check.py 17
```

After about a minute it reports `order 17: model verified on all 4913 triples (k=6, j=4)`. Its model has six squares and differs from the table in Lean, which has eight.

At order 26 the program needs to be told which pattern to try. Run in order, it reaches six squares with none fixed and stays there: a ten-minute run did not decide that pattern. With six squares and two of them fixed it finds a model in under a minute:

```sh
python3 Simple/check.py --pattern 6:2 26
```

It reports `order 26: model verified on all 17576 triples (k=6, j=2)`.

By default, the Python program reports CaDiCaL's results. To also replay each refutation with a separate certificate checker, use `lrat-trim` **0.2.1-rc3**, pinned to [revision `423194927df747528d5b7364806b5b77b2660c12`](https://github.com/arminbiere/lrat-trim/tree/423194927df747528d5b7364806b5b77b2660c12). This revision passed all 71 order-15 certificates. The script requires its `--rup` option, which version 0.2.0 does not support. Supply the path to that executable:

```sh
python3 Simple/check.py --verify-with /path/to/lrat-trim 15
```

This mode succeeds only if every certificate passes the checker, and reports `order 15: 71 cases, all RUP proofs verified`.

The square-row identity used in the reduction also appears in the [Equational Theories Project's E1486 notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/1486_graph_spectrum.md).
