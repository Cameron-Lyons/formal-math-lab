# Deterministic ordering of the translated F₃ model

A deterministic minimum-fill variable order shrinks the **monomial-cooccurrence graph** of the translated native-`F₃` model with `e3`. It is exported as a pure variable renaming, with no solver run, no new equations, no prefix restrictions, and no backend changes.

Two graphs need to be kept distinct. In the full polynomial-support graph, two variables share an edge if they appear anywhere in the same generator. That graph is already the complete graph **K95** (4,465 edges), because several moment generators (including `M2222 - 1`) contain all 95 coupled variables. Every order therefore has induced width 94 and zero fill, so there is no small factor-graph decomposition.

The finer monomial-cooccurrence graph connects two variables only when they appear in the **same monomial**, giving 868 edges. Because it ignores coupling across separate terms of an equation, its width is only a weaker heuristic rather than a width bound on the polynomial system.

## Measured elimination metrics

At each elimination step, connect all remaining neighbors of the chosen vertex, count the newly added fill edges, and remove the vertex. Induced width is the largest remaining neighborhood size across all steps:

| Order | Induced width | Added fill edges |
|---|---:|---:|
| Natural variable order | 51 | 2384 |
| Reverse variable order | 50 | 2304 |
| Minimum degree | 44 | 1231 |
| Minimum fill | **37** | **1077** |

Minimum fill picks the vertex with the fewest missing edges among its current neighbors (breaking ties by current degree, then original variable index); minimum degree swaps the first two criteria. All choices are deterministic with no randomized search, and they measure particular orders rather than proving optimal treewidth.

The exported variable list follows this elimination order. Because grevlex Gröbner-basis computation does not behave like graph elimination, smaller induced width does not guarantee a smaller basis, smaller F4 matrices, or faster runs.

## Exact exported input

The frozen source is `exact_f3_translation_e3.ms` (SHA256 `44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5`), with 96 variables and 176 generators. The independent apex-offset variable stays **last** at index 95 with its field equation intact.

- [Renamed complete input](exact_f3_order_selected.ms), SHA256 `b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`.
- [Complete forward/inverse map](exact_f3_order_selected.json), SHA256 `387d85417ffb7823ceef2984b506b39f6913169491d7ada2d75343ec1829bc3e`.
- [Graph metrics and adjacency certificate](exact_f3_order_audit.json).
- [Generator and checker](exact_f3_order.py).

The mapping file stores both `new_index -> old_index` and its inverse, tags every normalized-prefix coordinate, and gives all 100 original-color linear forms in the renamed variables. All coefficients, exponents, domains, and generator positions stay unchanged. Applying the inverse renaming reproduces the source `.ms` file **byte for byte**, and rebuilding the monomial graph on the renamed file reproduces width 37 and fill 1,077 in natural order.

The quotient dimension therefore still equals the full labeled count directly (multiplier and divisor 1), and the unrestricted count remains unknown.

```sh
python experiments/exact_f3_order.py --check
```
