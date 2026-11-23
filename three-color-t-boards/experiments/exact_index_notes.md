# Binary location indices for pattern occurrences

This checks the existing `binary` occurrence encoding on phased inputs.
It does not evaluate the unrestricted ternary count.

For each pattern, give every possible placement a different binary index.
An occurrence implies the bits of its index. Two distinct occurrences cannot
both hold, since at least one index bit would have contradictory values.
The pattern's at-least-one clause selects an occurrence, which fixes every
index bit uniquely. Thus these auxiliaries preserve ordinary model counts,
including when the number of candidate placements is not a power of two.

The implementation was already covered by the independent encoding checks
in `exact_count_check.py` and `exact_phase_check.py`. This experiment uses it
with the all-false-witness transformation to check whether changing the
placement representation warrants a larger counting run.

```sh
python experiments/exact_phase.py --colors 2 --occurrence-amo binary experiments/exact_index_binary.cnf
python experiments/exact_phase.py --seed 1 --prefix-rows 7 --normalize none --occurrence-amo binary experiments/exact_index_prefix_C.cnf
python experiments/exact_phase.py --occurrence-amo binary experiments/exact_index_ternary.cnf
python experiments/exact_reduced_benchmark.py --seconds 60 --jobs 2 --output experiments/exact_index_benchmark.json experiments/exact_index_binary.cnf experiments/exact_index_prefix_C.cnf
```

Both counting runs completed. The orbit-normalized binary count is **42**;
the published seven-row prefix C has **2** completions. Prefix C used 23.016
user CPU seconds and 34.555 wall seconds. This provides no improvement over
the previously recorded occurrence-tree result, so no unrestricted counting
trial was added for this encoding.

The generated unrestricted model has 7,630 variables and 82,097 clauses.
Its known witness was completely propagated and all clauses checked before
rephasing. Its presence on disk is a prepared exact instance, **not a completed
count or evidence that it was run**. Metadata accompany each `.cnf` file.
Commands and terminal results are in
[`exact_index_benchmark.json`](exact_index_benchmark.json).

The workspace was moved externally during this investigation. The original
path `/home/cam/three-color-t-boards` remains a symbolic link to
`/home/cam/formal-math-lab/three-color-t-boards`; generated absolute paths in
the latest run records resolve to the latter location.
