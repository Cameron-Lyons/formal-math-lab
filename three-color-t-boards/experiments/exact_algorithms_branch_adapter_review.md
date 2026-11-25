# Independent linear-branch adapter and prefix checks

The adapter audit passes for all four branches in both natural and
minimum-fill order. `exact_algorithms_branch_adapter_review.py` checks the
actual backend definition and CLI prepare-only output, not just the helper.
All eight input files match the frozen manifest byte for byte; their
metadata preserves the branch, ordinary F3 ring, 97 variables, 179+k
generators, bilinear original colors, and divisor/multiplier 1. It derives
the branch linears independently from the color forms and checks all 800
bilinear forms across the variants. Its 26 Python scope/type rejection
cases and four invalid CLI cases pass, including branch 0, which must not
be lost to a truthiness check. No solver is invoked by this audit.

`exact_algorithms_branch_six.py` then appends the 81 actual original-color
constraints `a+s*d_cell=color` separately to each natural-order branch.
All four bounded solver runs completed, with counts **[6, 0, 0, 0]** and
sum **6** for this fixed prefix. The prefix has Delta=[1,2,0,2], so only
branch 0 is possible; there a=s=1. Each input retains 97 variables and has
260+k generators. No normalization multiplier or field-extension divisor
is applied.

| Branch | Exact fixed-prefix count | Basis size | Solver CPU seconds | Solver wall seconds |
|---|---:|---:|---:|---:|
| 0 | 6 | 102 | 0.826184 | 0.896508 |
| 1 | 0 | 1 | 0.192465 | 0.241438 |
| 2 | 0 | 1 | 0.194969 | 0.240067 |
| 3 | 0 | 1 | 0.187696 | 0.239779 |

Every run used the unchanged reviewed seventh executable, exact serial
linear algebra, a pair-batch target of 16, a 30-second solver limit,
60-second whole-worker limit, and 2 GiB address-space limit. All exited
zero with exactly one completed-export marker, no error diagnostics, a
strictly parsed complete leading ideal, and agreement between both
independent Python integer counters. The three zero results are completed
unit ideals, not missing or timed-out counts.

Detailed provenance is in `exact_algorithms_branch_adapter_review.json`
and `exact_algorithms_branch_six_results.json`, with separate
`exact_algorithms_branch_six_{0,1,2,3}` inputs, constraints, logs, leading
ideals and result metadata. All worker processes are terminal. This
validates the branch adapter and specialization; it does not give an
unrestricted branch count. The full total requires exactly one completed
unrestricted count for each branch. Different variable orders must not
be added as separate contributions.

After these workers finished, the backend's common completion path was
corrected to set `standard_basis_complete=true` alongside
`basis_complete=true`. The workers had inherited the former flag as false
from prepared-model metadata, although their strict leading exports and
result status already correctly attested completion. The source change is
exactly this annotation addition; `exact_algorithms_branch_completion_fix.py`
verifies that removing it reproduces the previously audited backend hash.
No input/model handling changed.

The five owned small-fixture metadata files (these four and the prior
quintic sign fixture) were archived verbatim as `*.pre_flag_fix.json`.
Their current `.json` versions correct the stale flag and append an explicit
correction record. `exact_algorithms_branch_completion_fix.json` records
every original/corrected metadata hash. The correction reparsed all saved
completed exports and reran both exact integer counters, without invoking
a solver. Inputs, logs, basis/leading exports, counts, timings, and the
hashes of the adapters actually used for those runs remain unchanged.
All five current records have consistent true basis-completion flags,
including the three completed unit ideals. No unrestricted run artifact
was modified.
