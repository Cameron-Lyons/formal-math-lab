# Counting-polarity experiment

This experiment changes only Ganak's branching polarity on the same rephased,
orbit-normalized CNF `exact_phase_ternary.cnf`. It adds no board constraints
and keeps the symmetry multiplier 12. Every input clause is verified to contain
a negative literal, confirming that all-false satisfies the rephased formula.

Two deterministic policies were tested:

- `--polar 3`: `Counter::get_polarity` returns `true`, which becomes the
  **sign** of `Lit`. That picks negative literals (false Boolean assignments),
  even though the CLI help text describes option 3 as "true". Its initial
  decisions therefore match the known all-false witness.
- `--polar 1`: reads Ganak's `VarData.last_polarity`, which starts at `false`
  (positive literals, or true assignments) and updates during propagation. It
  is **not** seeded from the CryptoMiniSat startup model, so it does not start
  out following the all-false witness.

These details were checked in the pinned release source:
[`get_polarity` and `decide_lit`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L1453),
[`VarData`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/structures.hpp#L179),
and [`set_lit`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L4467).

Both options reproduced the full binary orbit count of **42** while counting
all variables directly, with 1,619 reported conflicts for option 3 and 1,623
for option 1. That verifies count preservation on the binary problem without
predicting ternary runtime.

The ternary runs used verbosity 2 (to log each learned-clause database
reduction), a 120-second wall limit, and a 512 MB cache limit. The script logs
CPU time separately because other experiments ran concurrently. Clause
reduction logs confirm that counting search started. Missing intermediate
counts or conflict summaries never mean a zero count, since Ganak does not
print each found model at this verbosity.

Run from the repository root:

```sh
python experiments/exact_phase_polar.py --seconds 120
```

`exact_phase_polar_results.json` stores input hashes, full commands, finished
counts or timeout statuses, CPU and wall times, memory usage, and logged
progress. The separate default-polarity baseline run is not modified by this
script.

Both ternary runs timed out without a count. Inside their 120-second wall
limits, option 1 used 25.937 CPU seconds and option 3 used 26.599 CPU seconds.
Both passed initial SAT and reached the fifth learned-clause database
reduction, and neither printed a periodic conflict total or intermediate count.
Both policies actively ran counting search, with no evidence of a speed
advantage or a completion-time estimate. Both processes have exited.
