# Independent linear-branch adapter and prefix checks

The adapter audit passes across all four branches in both natural and minimum-fill variable orders. `exact_algorithms_branch_adapter_review.py` checks both the backend definitions and the actual CLI prepare-only output, not just helper functions. All eight generated inputs match the frozen manifest byte for byte, keeping the branch ID, `F3` ring, 97 variables, `179 + k` generators, bilinear original-color forms, and divisor/multiplier of 1. The audit rederives the branch linear equations from the color forms, checks all 800 bilinear forms across the eight variants, and passes all 26 Python scope/type rejection tests plus 4 invalid CLI tests (including branch 0, ensuring a truthiness check cannot drop it). Neither this script nor the manifest check runs a solver.

`exact_algorithms_branch_six.py` then appends the 81 original-color equations `a + s*d_cell = color` to each natural-order branch and runs the solver on each. All four bounded runs finished cleanly with counts **[6, 0, 0, 0]**, summing to **6** for this fixed prefix. Because the prefix has `Delta = [1, 2, 0, 2]`, only branch 0 is satisfiable (with `a = s = 1`). Each input has 97 variables and `260 + k` generators, with no extra multiplier or field-extension divisor.

| Branch | Exact fixed-prefix count | Basis size | Solver CPU seconds | Solver wall seconds |
|---|---:|---:|---:|---:|
| 0 | 6 | 102 | 0.826184 | 0.896508 |
| 1 | 0 | 1 | 0.192465 | 0.241438 |
| 2 | 0 | 1 | 0.194969 | 0.240067 |
| 3 | 0 | 1 | 0.187696 | 0.239779 |

All four runs used the unchanged reviewed seventh executable with exact serial linear algebra, pair-batch target 16, a 30-second solver timeout, a 60-second worker timeout, and a 2 GiB address-space cap. Each exited 0 with one completion marker, no errors, a strictly parsed leading ideal, and matching counts from both independent Python integer counters. The three zeros are completed unit ideals, not missing or timed-out runs.

Full provenance is stored in `exact_algorithms_branch_adapter_review.json` and `exact_algorithms_branch_six_results.json`, alongside per-branch files `exact_algorithms_branch_six_{0,1,2,3}` (inputs, constraints, logs, leading ideals, and metadata). All worker processes have finished. This checks the adapter and fixed-prefix specialization only; an unrestricted total still needs one completed unrestricted count for each of the four branches (without summing different variable orders of the same branch).

After these runs finished, we fixed a metadata bug in the backend's common completion path so it sets `standard_basis_complete=true` together with `basis_complete=true`. Earlier runs had inherited `standard_basis_complete=false` from the prepared-model metadata even though their leading exports and status already confirmed completion. `exact_algorithms_branch_completion_fix.py` verifies that removing that single line restores the previously audited backend hash, with no change to input or model handling.

The five affected small-fixture metadata files (these four plus the earlier quintic sign fixture) were saved verbatim as `*.pre_flag_fix.json`. Their updated `.json` files fix the stale flag and append a correction entry, with all before/after hashes logged in `exact_algorithms_branch_completion_fix.json`. The fix script reparsed every saved export and reran both Python counters without invoking any solver. Inputs, logs, leading exports, counts, timings, and recorded adapter hashes stayed untouched, and no unrestricted artifact was modified. All five records now have consistent `true` completion flags, including the three completed unit ideals.
