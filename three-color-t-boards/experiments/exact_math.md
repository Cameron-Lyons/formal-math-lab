# Structural reductions for the unrestricted exact count

This note proves necessary conditions and exact counting identities. It does **not** evaluate the unrestricted ternary count.

## Every ternary symmetry orbit has exactly twelve boards

Let `Q = {0, 1, 2}`, and let `S_3 × C_2` act by global color permutations and horizontal reflection. Every valid board uses all three colors, so only the identity color permutation can fix a valid board without reflection.

Now suppose a recolored reflection `(π, R)` fixes a valid board. Squaring it shows `π²` fixes the board, so `π² = id`, meaning `π` is either the identity or a transposition. Validity gives a bijection from the 81 T placements to `Q⁴`, intertwining `R` on placements with

```
(t, l, m, r) ↦ (π(t), π(r), π(m), π(l))
```

on patterns. Both actions must have the same number of fixed points. Reflection fixes 9 placements (the center T in each of the 9 non-apex rows). If `π` fixes `f` colors, a fixed pattern has `f` choices for `t`, `f` choices for `m`, 3 choices for `l`, and `r = π(l)` forced, giving `3 f²` fixed patterns: 27 for the identity and 3 for a transposition. Neither equals 9, a contradiction.

The symmetry action is therefore free, and the unrestricted labeled count is exactly 12 times the orbit count, with no stabilizer exceptions. More generally, the same argument rules out any recolored reflection on an `n`-color ziggurat unless the color involution fixes `f` colors with `f² = n`.

## The remaining patterns form prescribed-length trails

Map each ordered pattern `(t, l, m, r)` to the directed edge

```
(l, m) → (m, r)
```

in the 9-vertex de Bruijn multigraph (3 distinct copies of each of the 27 edges, distinguished by top color `t`). Every vertex has in-degree and out-degree 9. Board row `r` traces a trail of length `2r - 1` from `(a_r(0), a_r(1))` to `(a_r(2r - 1), a_r(2r))`, so across a full valid board the multiset of row-start pairs matches the multiset of row-end pairs.

After fixing rows 0 through `k`, delete all used edges. The remaining rows must form edge-disjoint trails in the residual graph of lengths

```
2k + 1, 2k + 3, ..., 17.
```

This yields a tighter pruning test than total degree imbalance alone:

1. Drop isolated vertices and find the weak connected components of the residual graph.
2. Because each future row stays inside one weak component, the remaining row lengths must partition across the components so each subset sums to its component's edge count.
3. Each active component needs at least `max(1, sum_v max(outdegree(v) - indegree(v), 0))` trails, so its assigned subset must have at least that many rows.

With at most 9 vertices and 9 remaining rows, component detection plus a subset-mask DP is cheap. It is necessary only, not sufficient: top colors along each trail must also match the previous board row, and trail lengths must match row by row. Every remaining row length is odd, so each active component's edge-count parity must match its assigned row count (already implied by the subset-sum check).

## Exact transfer recurrence and its limitation

For a row word `u` of length `2r + 1` and a used-pattern set `S`, let `F_r(u, S)` count valid partial boards through row `r` ending in `u` with pattern set `S`. Start from

```
F_0([c], ∅) = 1   for c in Q.
```

For each candidate next row `v` of length `2r + 3`, form

```
W(u, v) = [(u[j], v[j], v[j+1], v[j+2]) : 0 ≤ j ≤ 2r].
```

Whenever these `2r + 1` patterns are pairwise distinct and disjoint from `S`, add

```
F_{r+1}(v, S ∪ set(W(u, v))) += F_r(u, S).
```

The unrestricted labeled count is

```
Σ_u F_9(u, Q⁴).
```

Deleting the last row uniquely recovers the predecessor state, so this recurrence merges all interchangeable caps automatically and counts every valid board once.

Unlike sampling selected six-row prefixes, this recurrence is exact and exhaustive, yet it is far too large to run directly for three colors: even before pruning or merging, five rows have $3^{25} = 282,429,536,481$ assignments and six rows have $3^{36} = 150,094,635,296,999,121$. Symmetry breaking alone does not overcome that growth, and residual-component pruning mostly kicks in late when many patterns are already used.

## A smaller exact parametrization by boundary colors and local permutations

Scan cells in row-major order. The apex and the first two cells of each non-apex row form 19 free boundary digits. Every remaining cell finishes a T whose first three colors `(t, l, m)` are already fixed. Recording the order in which the three right colors appear for each of the 27 triples `(t, l, m)` gives 27 permutations in `S_3`.

Conversely, given 19 boundary digits and 27 permutations in `S_3`, fill the board row by row, pulling the next unused right color from the permutation for `(t, l, m)` and rejecting if any triple occurs a fourth time. If the scan completes, all 81 slots filled without overflowing any capacity-3 triple, so every pattern occurs once and the tuple recovers uniquely from the board.

Letting `A(b, σ)` be 1 if the scan accepts and 0 otherwise, the exact labeled count is

```
Σ_{b ∈ Q^19} Σ_{σ ∈ (S_3)^27} A(b, σ).
```

This shrinks the ambient space from `3^100` to `3^19 * 6^27` (~`1.19 × 10^30`), still far too large to enumerate, and the acceptance test `A(b, σ)` cannot be dropped because arbitrary tuples overflow.

`exact_math_rotors.py` exhausts all 131,072 binary tuples, accepts exactly 168 boards matching the published cell-by-cell enumerator board for board, checks all 168 in Cartesian coordinates, round-trips every accepted board back to its tuple, and round-trips all five published ternary witnesses:

```sh
python experiments/exact_math_rotors.py
```

## Component-pruning experiment

`exact_math_search.cpp` copies `../splice_search.cpp` (leaving the original unchanged) and adds the residual weak-component and length-partition pruning above across three build modes:

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror -DEXACT_COMPONENT_PRUNE=0 experiments/exact_math_search.cpp -o /tmp/exact_math_baseline
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_math_search.cpp -o /tmp/exact_math_components
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror -DEXACT_COMPONENT_LOOPS_ONLY=1 experiments/exact_math_search.cpp -o /tmp/exact_math_loops
```

The third mode checks only isolated homogeneous-triple loops: if some `(t, 0, 0, 0)` remains unused while no bridge triple `001, 002, 100, 200` remains, vertex `00` is stuck in a component of at most 3 edges, whereas every future row needs at least 11 edges (and similarly for `11` and `22`). That bitmask check catches nearly all component rejections.

All three versions exhausted two saved six-row prefixes and matched their **complete ordered tail lists byte for byte** in `splice_witnesses.json` (validating those two fibers only):

| Saved group | Prefix | Exact tails |
|---|---|---:|
| 1 | `000000100002011001202102210110211112` | 138 |
| 3 | `000000100011210120112122000122221202` | 36 |

| Group | Row-8 calls | Full component rejections | Isolated-loop rejections |
|---|---:|---:|---:|
| 1 | 34,001,614 | 238,574 | 238,569 |
| 3 | 42,059,981 | 187,720 | 187,702 |

At row 9, full component pruning rejected 10,296 of 51,486 states in group 1 and 5,236 of 21,294 in group 3, while isolated-loop pruning caught 9,460 and 5,074; neither pruned anything at rows 6 or 7.

Fresh CPU comparisons between baseline and isolated-loop pruning:

| Group | Baseline CPU seconds | Isolated-loop CPU seconds |
|---|---:|---:|
| 1 | 15.792244 | 15.309328 |
| 3 | 20.978890 | 21.356523 |

Because it sped up group 1 slightly and slowed down group 3 slightly, it gives no reliable speedup. A 4 MiB lookup table of all 21-edge undirected support graphs (`-DEXACT_COMPONENT_LOOKUP=1`) also kept exact counts and ran slower. Wall times in `exact_math_benchmark_group*.log` ran under concurrent load and are not controlled benchmarks.

One unimplemented follow-up would detect isolated loops mid-row as soon as the last bridge edge is consumed: if any `aaa` patterns remain, later rows are too long to use them, so the current row must be sitting at pair `aa` with its remaining length matching the unused `aaa` count (a two-ended row search would need a separate check for both active ends).
