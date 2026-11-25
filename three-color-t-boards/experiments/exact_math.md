# Structural reductions for the unrestricted exact count

This note establishes necessary conditions and exact identities. It does **not**
evaluate the unrestricted ternary count.

## Every ternary symmetry orbit has exactly twelve boards

Let the palette be `Q={0,1,2}`. The group `S_3 × C_2` acts by a global
color permutation and optional horizontal reflection. A valid board uses every
color, so a pure color permutation can fix it only if it is the identity.

Suppose a recolored reflection `(π,R)` fixes a valid board. Squaring this
operation shows that `π²` fixes the board, hence `π²=id`. Thus `π` is either
the identity or a transposition. Validity supplies a bijection from the 81
placements to `Q⁴`. This bijection intertwines the action of `R` on placements
with the action

```
(t,l,m,r) ↦ (π(t),π(r),π(m),π(l))
```

on patterns. Their fixed-point counts must agree. There are nine fixed
placements: the central placement in each of the nine non-apex rows. If
`f` is the number of fixed colors of `π`, a fixed pattern has `f` choices
for each of `t,m`, three choices for `l`, and the uniquely determined
`r=π(l)`. Consequently there are `3 f²` fixed patterns. For the identity
this is 27, and for a transposition it is 3. Neither equals nine, a
contradiction.

Thus the group action is free, and the exact labeled count is twelve times
the exact orbit count. No stabilizer correction or exceptional orbit can
occur. More generally the same proof excludes recolored reflections for
an `n`-color ziggurat unless the involution has `f²=n` fixed colors.

## The remaining patterns form prescribed-length trails

Project an ordered pattern `(t,l,m,r)` to the directed edge

```
(l,m) → (m,r).
```

The resulting multigraph has nine vertices and three copies of each of the
27 de Bruijn edges. It is balanced: every vertex has indegree and outdegree
nine. The patterns in board row `r` form a trail of length `2r−1`, with
initial vertex `(a_r(0),a_r(1))` and terminal vertex
`(a_r(2r−1),a_r(2r))`. The edge copies remain distinct by their top color.
In particular, across a complete valid board the multiset of initial
pairs equals the multiset of terminal pairs.

After rows 0 through `k` have been fixed, delete all used pattern edges.
Every future row must be a trail in this residual graph, and their lengths
are exactly

```
2k+1, 2k+3, …, 17.
```

This gives a useful stronger pruning condition than just bounding the total
positive degree imbalance:

1. Discard isolated vertices with no remaining edge and find the residual
   graph's weak components.
2. A trail lies entirely in one weak component. Therefore each component's
   edge count must be the sum of a subset of the remaining row lengths,
   with the subsets partitioning those lengths.
3. A component with at least one edge needs at least
   `max(1, sum_v max(outdegree(v)−indegree(v),0))` trails. Its assigned
   subset must contain at least this many row lengths.

There are at most nine vertices and nine remaining row lengths. Component
finding and a subset-mask dynamic program therefore implement this condition
cheaply. It is necessary, not sufficient: the upper colors of the edges in
a future row must also spell the preceding board row, and trails must have
the specified lengths. Ignoring that compatibility would count objects that
are not boards.

A further necessary check at each boundary is that every active component
has an edge-count parity equal to the parity of the number of rows assigned
to it, since every remaining row length is odd. The subset-mask condition
already includes this check.

## Exact transfer recurrence and its limitation

For a word `u` of length `2r+1` and a set `S` of used ordered patterns, let
`F_r(u,S)` be the number of valid partial boards through row `r` having last
row `u` and pattern set `S`. The initial values are

```
F_0([c],∅)=1  for c in Q.
```

Given a candidate next row `v` of length `2r+3`, define

```
W(u,v) = [(u[j],v[j],v[j+1],v[j+2]) : 0≤j≤2r].
```

If these `2r+1` patterns are distinct and disjoint from `S`, perform the
integer update

```
F_{r+1}(v,S ∪ set(W(u,v))) += F_r(u,S).
```

The unrestricted labeled count is exactly

```
Σ_u F_9(u,Q⁴).
```

This recurrence merges all interchangeable caps automatically and requires
only the last row and the used pattern set. Its proof is by unique deletion
of the last row: every transition creates a valid partial board, and every
valid partial board is created exactly once from its predecessor.

The recurrence is exhaustive, unlike enumerating a list of selected six-row
prefixes. It has not been evaluated for the ternary instance. Even five
rows have 25 cells and `3^25=282,429,536,481` unrestricted assignments before
pruning and merging, while six rows have `3^36=150,094,635,296,999,121`.
The symmetry reduction alone does not eliminate this bottleneck. The
residual-component test helps principally when many patterns have already
been used; it does not by itself make the unrestricted recurrence practical.

## A smaller exact parametrization by boundary colors and local permutations

Read cells in row-major order. The apex and the first two cells of each
non-apex row are free boundary cells, giving 19 boundary digits. Every
other cell completes a T whose first three colors `(t,l,m)` are already
known. For each of the 27 triples `(t,l,m)`, record the order in which its
three right colors appear in the complete scan. In a valid board these
right colors form a permutation of `Q`.

Thus every valid board gives 19 boundary digits and 27 permutations from
`S_3`. Conversely, given these data, fill the board in row-major order,
using the next unused output from the permutation indexed by `(t,l,m)`.
Reject if one triple is encountered a fourth time. If the scan finishes,
all 81 pattern slots have been used; since there are 27 triples with
capacity three, each has occurred exactly three times. Every pattern then
occurs exactly once. The data are recovered uniquely from the completed
board, so this is a bijection between valid boards and accepted inputs of
the deterministic procedure.

Consequently, if `A(b,σ)` is 1 when that procedure finishes and 0 otherwise,
then the exact labeled count is

```
Σ_{b∈Q^19} Σ_{σ∈(S_3)^27} A(b,σ).
```

This reduces the ambient parameter space from `3^100` to `3^19·6^27`, but
the latter is still about `1.19×10^30`. It is an exact parametrization,
not an evaluated answer. Most importantly, the acceptance condition cannot
be dropped: arbitrary local output permutations need not yield a board.

The independent implementation in `exact_math_rotors.py` exhausts all 131,072
binary parameter tuples. Exactly 168 are accepted; their complete board set
matches the supplied cell-by-cell enumerator. Each accepted board also passes
a coordinate-based geometric check and round-trips to its original tuple.
All five supplied ternary witnesses round-trip as well. Run:

```sh
python experiments/exact_math_rotors.py
```

## Component-pruning experiment

`exact_math_search.cpp` copies the fixed-six-row-prefix search into an
experimental file, leaving `../splice_search.cpp` unchanged. It implements
the residual weak-component and prescribed-length test above. Three build
settings permit comparison:

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror -DEXACT_COMPONENT_PRUNE=0 experiments/exact_math_search.cpp -o /tmp/exact_math_baseline
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_math_search.cpp -o /tmp/exact_math_components
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror -DEXACT_COMPONENT_LOOPS_ONLY=1 experiments/exact_math_search.cpp -o /tmp/exact_math_loops
```

The last version checks just isolated homogeneous-triple loops. For example,
if any `(t,0,0,0)` remains but no lower triple `001`, `002`, `100`, or `200`
remains, pair `00` forms a component with at most three edges. Every future
row has at least eleven edges, so completion is impossible. The tests for
`11` and `22` are analogous. This detects almost all observed component
failures with only a few bit masks.

Both prefixes were exhausted, and every version reproduced the **complete
ordered tail list byte for byte** from `splice_witnesses.json`:

| Saved group | Prefix | Exact tails |
|---|---|---:|
| 1 | `000000100002011001202102210110211112` | 138 |
| 3 | `000000100011210120112122000122221202` | 36 |

These are exact counts of the stated prefix fibers only. They impose no
restriction on the number of boards outside those fibers.

| Group | Row-8 calls | Full component rejections | Isolated-loop rejections |
|---|---:|---:|---:|
| 1 | 34,001,614 | 238,574 | 238,569 |
| 3 | 42,059,981 | 187,720 | 187,702 |

The full test also rejected 10,296 of 51,486 row-9 states for group 1, and
5,236 of 21,294 for group 3. The isolated-loop version rejected 9,460 and
5,074, respectively. Neither test rejected any row-6 or row-7 state in
these runs.

Fresh CPU-time measurements compare the original algorithm with the cheap
isolated-loop version:

| Group | Baseline CPU seconds | Isolated-loop CPU seconds |
|---|---:|---:|
| 1 | 15.792244 | 15.309328 |
| 3 | 20.978890 | 21.356523 |

The gain in one case and loss in the other do **not** demonstrate a reliable
acceleration. A separate 4 MiB table of all 21-edge undirected support graphs
was also tested (`-DEXACT_COMPONENT_LOOKUP=1`); it preserved all counts but
was slower. Several other searches were active on the machine, so the saved
wall times should not be interpreted as controlled performance measurements.
The complete per-run diagnostics are in `exact_math_benchmark_group*.log`.

A possible next refinement is to detect an isolated loop when its last
non-loop bridge is consumed during a row, rather than waiting until the
row is complete. If unused `aaa` patterns remain, later rows are too long
to cover them. The current row must therefore now be at pair `aa`, with
remaining length exactly equal to the number of unused `aaa` patterns.
This observation has not been implemented or benchmarked here. A two-ended
row search needs a separate argument for its two active fronts.
