# Exact counting by direct comparison of T placements

The unrestricted ternary count is still undetermined. This experiment replaces
the placement-to-pattern table with direct inequalities between placements.
It reduces formula size but has not demonstrated a counting speedup.

## Equivalence and unique auxiliaries

There are exactly `q^4` T placements and exactly `q^4` possible ordered color
patterns. Therefore a well-formed board is valid precisely when no two
placements carry the same pattern.

For each pair of cells needed in a comparison, introduce a shared Boolean
`E(i,j)` meaning that their colors agree. If their one-hot color indicators
are `x[i,a]` and `x[j,b]`, impose

```text
not x[i,a] OR not x[j,b] OR (E(i,j) if a=b else not E(i,j)).
```

Exactly one pair `(a,b)` is active, so these clauses uniquely fix `E(i,j)`.
For every pair of T placements, add a clause requiring at least one of their
four corresponding cell pairs to differ. Shared comparisons are encoded once.
Known fixed cells simplify comparisons to constants or cell indicators.

This is a bijection between models and valid boards: a board determines all
comparison variables, while satisfying all comparison clauses gives distinct
patterns at all placements. Ordinary model counting requires no projection.
The optional cell-variable support is count preserving. Existing palette and
reflection normalization select one representative per symmetry orbit; the
unrestricted ternary count is twelve times the normalized count.

The phased models use the already verified Boolean complementation from
`exact_phase.py`. They represent the entire original solution set, with a
known complete model mapped to the all-false assignment. The witness data
retain the attribution documented in the source certificates.

## Validation

```sh
python experiments/exact_compare_check.py
```

All **27** exact-count checks passed. They include the one-color case,
unrestricted binary **168**, palette-normalized **84**, orbit-normalized
**42**, all sixteen first-two-row binary fibers against the independent
published enumerator, five fully fixed ternary boards, rejection of the
uniform-triple counterexample, and preservation of binary 42 after rephasing.
All five known ternary witnesses also extend to complete, verified auxiliary
assignments in the unrestricted normalized formula. See
[`exact_compare_check.log`](exact_compare_check.log).

## Size and bounded computation

| Model | Variables | Clauses |
|---|---:|---:|
| Unrestricted ternary, orbit normalized | 5,382 | 50,363 |
| Published seven-row prefix C | 1,413 | 13,786 |

The unrestricted model uses 4,880 shared cell-equality variables and 3,240
placement-pair comparisons. The earlier occurrence model uses 13,543
variables and 62,090 clauses; smaller size alone does not establish faster
counting or stronger propagation.

```sh
python experiments/exact_compare_cnf.py --orbit-canonical --independent-support --phase-seed 0 experiments/exact_compare_ternary.cnf
python experiments/exact_compare_cnf.py --prefix-json sources/anc/certificates.json --prefix-name C --independent-support --phase-seed 1 experiments/exact_compare_prefix_C.cnf
python experiments/exact_reduced_benchmark.py --seconds 60 --jobs 2 --output experiments/exact_compare_benchmark.json experiments/exact_compare_prefix_C.cnf experiments/exact_compare_ternary.cnf
```

The existing bounded benchmark wrapper is also applicable to these formulas;
its log filenames retain its `exact_reduced_bench_` prefix. Both runs entered
counting and ended at the 60-second wall limit with exit code 124. The full
run used 25.116 user CPU seconds; prefix C used 25.547. Neither returned an
exact count, including the prefix whose count is independently known to be
two. All processes ended. Full commands, terminal statuses and timing data
are in [`exact_compare_benchmark.json`](exact_compare_benchmark.json).
