# Counting-polarity experiment

The experiment changes only Ganak's branching policy on the same witnessed,
orbit-normalized CNF `exact_phase_ternary.cnf`. It adds no board restriction
and leaves the count multiplier 12 unchanged. Every input clause is checked
to contain a negative literal, independently confirming that all-false is a
satisfying assignment of the rephased formula.

Two deterministic policies are compared:

- `--polar 3`: `Counter::get_polarity` returns `true`, which is passed as the
  **sign** of `Lit`. Thus it selects negative literals, i.e. false Boolean
  assignments, despite the CLI help describing option 3 as "true". Its first
  preferred decisions agree with the known all-false witness.
- `--polar 1`: uses Ganak's `VarData.last_polarity`. This field starts `false`
  (positive literals / true assignments), and propagated assignments update
  it. It is **not** initialized from the independent CMS solver's model, so
  it does not initially follow the all-false witness.

These details are checked in the exact release sources:
[`get_polarity` and `decide_lit`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L1453),
[`VarData`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/structures.hpp#L179),
and [`set_lit`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L4467).

Both options reproduced the full binary orbit count **42**, counting all
variables directly. They had respectively 1,619 and 1,623 reported conflicts
for options 3 and 1. This verifies count preservation on the complete binary
problem; it does not predict ternary runtime.

The ternary runs use verbosity 2 to report each learned-clause database
reduction, with a 120-second wall limit and 512 MB cache limit. The script
records CPU usage separately because other experiments run concurrently.
The reduction messages prove that actual counting search has begun. Missing
intermediate counts or conflict summaries are not zero counts: the solver
does not report each discovered model at this verbosity.

Run from the repository root:

```sh
python experiments/exact_phase_polar.py --seconds 120
```

`exact_phase_polar_results.json` records input hashes, full commands, exact
completed counts or explicit timeout statuses, CPU and wall times, memory,
and reported progress. The baseline default-polarity run is managed separately
and is not altered by this experiment.

Both ternary trials timed out without a completed count. Option 1 used
25.937 CPU seconds and option 3 used 26.599 CPU seconds during their
120-second wall budgets. Both passed initial SAT and reached the fifth
reported learned-clause database reduction. Neither emitted a periodic exact
conflict total or an intermediate count. These observations establish active
counting search under both policies; they establish neither a runtime
advantage nor a completion-time estimate. Both benchmark processes ended.
