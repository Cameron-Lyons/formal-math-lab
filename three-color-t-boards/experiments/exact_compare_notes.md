# Exact counting by direct comparison of T placements

The unrestricted ternary count is still open. This experiment replaces the placement-to-pattern table with direct pairwise inequalities between placements. The formula is much smaller, though it did not finish faster in bounded tests.

## Equivalence and unique auxiliaries

Because there are `q^4` T placements and `q^4` ordered color patterns, a well-formed board is valid if and only if no two placements share the same pattern.

For each pair of cells that must be compared, introduce one shared Boolean variable `E(i,j)` asserting that cells `i` and `j` have the same color. Using the one-hot color indicators `x[i,a]` and `x[j,b]`, add:

```text
not x[i,a] OR not x[j,b] OR (E(i,j) if a=b else not E(i,j)).
```

Exactly one pair `(a,b)` is true, so `E(i,j)` is uniquely forced. Then, for each pair of placements, add one clause requiring at least one of their four matching cell pairs to disagree. Each shared cell pair is encoded once, and fixed cells simplify directly to constants or single literals.

This gives a one-to-one correspondence between models and valid boards: every board fixes all `E(i,j)`, and satisfying the inequality clauses forces all `q^4` patterns to be distinct. Ordinary model counting needs no projection, and optional cell-variable support preserves the count. Palette and reflection symmetry breaking pick one representative per orbit, so the unrestricted ternary count is 12 times the normalized count.

Phased models apply the verified Boolean flip from `exact_phase.py`, mapping a known valid board to the all-false assignment while preserving the full solution set. Witness data keep the attribution noted in the source certificates.

## Validation

```sh
python experiments/exact_compare_check.py
```

All **27** exact-count checks passed: the one-color board (1), unrestricted binary (**168**), palette-normalized binary (**84**), orbit-normalized binary (**42**), all 16 binary two-row fibers against the published enumerator, five fully fixed ternary boards, rejection of the uniform-triple counterexample, and preservation of binary 42 after rephasing. All five published ternary witnesses also extend cleanly to verified assignments in the unrestricted normalized formula (see [`exact_compare_check.log`](exact_compare_check.log)).

## Size and bounded computation

| Model | Variables | Clauses |
|---|---:|---:|
| Unrestricted ternary, orbit normalized | 5,382 | 50,363 |
| Published seven-row prefix C | 1,413 | 13,786 |

The unrestricted model uses 4,880 shared cell-equality variables and 3,240 placement-pair inequalities, down from 13,543 variables and 62,090 clauses in the occurrence encoding. Smaller formulas do not automatically yield stronger propagation or faster counting.

```sh
python experiments/exact_compare_cnf.py --orbit-canonical --independent-support --phase-seed 0 experiments/exact_compare_ternary.cnf
python experiments/exact_compare_cnf.py --prefix-json sources/anc/certificates.json --prefix-name C --independent-support --phase-seed 1 experiments/exact_compare_prefix_C.cnf
python experiments/exact_reduced_benchmark.py --seconds 60 --jobs 2 --output experiments/exact_compare_benchmark.json experiments/exact_compare_prefix_C.cnf experiments/exact_compare_ternary.cnf
```

The benchmark wrapper runs unchanged (so its logs keep the `exact_reduced_bench_` prefix). Both runs reached counting and timed out at 60 wall seconds with exit code 124 (25.116 user CPU seconds on the full run, 25.547 on prefix C). Neither returned a count, even on prefix C where the exact answer is 2. All processes have exited; exact commands, statuses, and timings are in [`exact_compare_benchmark.json`](exact_compare_benchmark.json).
