# Binary location indices for pattern occurrences

This experiment tests the existing `binary` occurrence encoding on rephased CNFs. It does not compute the unrestricted ternary count.

For each pattern, assign every candidate placement a distinct binary index, and add clauses making each occurrence imply its index bits. Two different occurrences then conflict on at least one bit, while the pattern's at-least-one clause forces an occurrence that uniquely fixes every bit. These auxiliaries preserve ordinary model counts even when the number of placements is not a power of 2.

`exact_count_check.py` and `exact_phase_check.py` already verified this encoding. Here we pair it with the all-false witness shift to test whether changing the placement encoding is fast enough to warrant a full run:

```sh
python experiments/exact_phase.py --colors 2 --occurrence-amo binary experiments/exact_index_binary.cnf
python experiments/exact_phase.py --seed 1 --prefix-rows 7 --normalize none --occurrence-amo binary experiments/exact_index_prefix_C.cnf
python experiments/exact_phase.py --occurrence-amo binary experiments/exact_index_ternary.cnf
python experiments/exact_reduced_benchmark.py --seconds 60 --jobs 2 --output experiments/exact_index_benchmark.json experiments/exact_index_binary.cnf experiments/exact_index_prefix_C.cnf
```

Both benchmark runs finished: orbit-normalized binary gave **42**, and published seven-row prefix C gave **2** in 23.016 user CPU seconds (34.555 wall seconds). Because that did not beat the occurrence-tree encoding, we did not run the unrestricted ternary formula.

The prepared unrestricted CNF has 7,630 variables and 82,097 clauses (its known witness propagated cleanly and passed all clause checks before rephasing). Keeping it on disk only saves a prepared exact input; it was never run and produces no count. Each `.cnf` has companion metadata, and exact commands and outputs are in [`exact_index_benchmark.json`](exact_index_benchmark.json).

Note: the workspace moved externally during these runs. `/home/cam/three-color-t-boards` stays a symlink to `/home/cam/formal-math-lab/three-color-t-boards`, so newer logs record absolute paths under the latter path.
