# Deterministic ordering of the translated F₃ model

A deterministic minimum-fill ordering improves the **monomial-cooccurrence
graph** of the translated native-F₃ model with `e3`. It has been exported as
a pure variable renaming. No solver, new equations, prefix restrictions, or
backend changes are involved.

The distinction between two graphs is essential. In the ordinary
polynomial-support graph, two variables are adjacent if they appear anywhere
in the same generator. That graph is already **K95**, with 4465 edges: many
individual moment generators, including `M2222−1`, use all 95 coupled
variables. Every order has induced width 94 and adds no edges. There is no
small factor-graph width or decomposition here.

The finer graph puts an edge only between variables appearing together in
the **same monomial**. It has 868 edges. It ignores coupling between different
terms of a global equation; therefore its width is a weaker input heuristic,
not a width bound for the complete polynomial factor graph.

## Measured elimination metrics

At each elimination step, connect all remaining neighbors of the selected
vertex, count newly added edges, and then remove that vertex. Induced width is
the maximum number of remaining neighbors at any step.

| Order | Induced width | Added fill edges |
|---|---:|---:|
| Natural variable order | 51 | 2384 |
| Reverse variable order | 50 | 2304 |
| Minimum degree | 44 | 1231 |
| Minimum fill | **37** | **1077** |

Minimum fill selects the smallest number of missing edges among current
neighbors, breaking ties by current degree and then original variable index.
Minimum degree reverses the first two criteria. All choices are deterministic;
no randomized ordering search was performed. These are widths of particular
orders, not proofs of the graph's optimal treewidth.

The exported variable list follows the selected graph-elimination sequence.
A grevlex Gröbner-basis calculation is not graph elimination, so these metrics
do not establish reduced basis size, smaller F4 matrices, or faster runtime.

## Exact exported input

The frozen source is `exact_f3_translation_e3.ms`, SHA256
`44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5`.
It has 96 variables and 176 generators. The independent apex-offset variable
stays **last**, at index 95, and its field domain remains present.

- [Renamed complete input](exact_f3_order_selected.ms), SHA256
  `b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`.
- [Complete forward/inverse map](exact_f3_order_selected.json), SHA256
  `387d85417ffb7823ceef2984b506b39f6913169491d7ada2d75343ec1829bc3e`.
- [Graph metrics and adjacency certificate](exact_f3_order_audit.json).
- [Generator/checker](exact_f3_order.py).

The map lists both `new_index→old_index` and its full inverse, identifies each
normalized-prefix coordinate, and provides every original-color linear form
in the renamed variables. All coefficients, exponents, domains, and generator
ordering are preserved. Every old and new polynomial is parsed and compared
under the permutation. Applying the inverse renaming recovers the complete
source input **byte for byte**. Rebuilding the monomial graph after renaming
also reproduces width 37 and fill 1077 under its natural order.

Thus the input still represents the full labeled count with multiplier and
divisor one. The unrestricted dimension remains unevaluated.

```sh
python experiments/exact_f3_order.py --check
```
