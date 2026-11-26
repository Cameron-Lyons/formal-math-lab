# Strict aggregation of the four linear sign branches

`exact_sign_branch_aggregate.py` takes one completed backend result for each of
branches 0, 1, 2, and 3, audits every saved artifact, and sums the four counts.
No unrestricted branch has finished as part of this work, so the total remains
unknown. The script never starts a solver.

Sixteen frozen inputs across two reviewed manifests are supported:

- `exact_f3_sign_branches_manifest.json`, hash
  `9ecb49f828699a3966c0349bddb4bc4f57cc163b65ba1855770357bf2e39d2c7`;
- `exact_f3_branch_elimination_manifest.json`, hash
  `91e25ac8803be65a12998e344060e3e48778e499722f30aaf7b5a663f8b2eaa0`.

Natural vs. minimum-fill variable orders and uneliminated vs. affine-eliminated
forms are alternative models of the same branch. Submitting two results for the
same branch ID is rejected even when their dimensions match. The elimination
manifest must point back to the pinned original partition as its source; all
other representations are rejected.

Every accepted input must match its reviewed source byte for byte, use
canonical variable names, and work over characteristic 3. An uneliminated
branch has 97 variables and `179+branch_id` generators; an affine-eliminated
branch has `n = 96-branch_id` variables and `177-branch_id` generators. The
basis parser, leading-export checks, and both integer counters use this checked
variable count. Original-color formulas, affine constants, pivot lists, and
variable maps are verified against the pinned metadata.

No original cells are fixed. Both independent symmetry variables stay in the
ring: offset at index `n-2` and sign at `n-1` (indices 95 and 96 when
uneliminated). In an eliminated branch, a canonical color form can have a
constant term, so the original-color formula can include a linear sign term as
well as bilinear terms, all kept in the model metadata. Because the factors of
3 and 2 already live inside the quotient dimension, both divisor and multiplier
are 1, and every full branch dimension must be divisible by 6.

To accept a branch result, the auditor checks `COMPLETE` status, integer exit
code 0, a completed basis flag, the unique export attestation, and the absence
of conflicting completion flags or backend errors. The solver log must contain
exactly one anchored `MSOLVE_PRIME_GB_EXPORT_COMPLETE` line and no error
diagnostics. The recorded command must specify ordinary g1 export, exact LA2,
1 thread, reduced basis, and the exact input and basis paths. Only reviewed
executable hashes from builds 7 and 8 are accepted, checking both the current
executable and local library bytes. If an outer-process record exists, it must
also confirm normal exit with no timeout.

The auditor strictly parses the basis file's hash, header, variable order,
field, monomial order, and generator list, and checks that the leading-ideal
JSON matches both that parse and the input/executable provenance. Both Python
arbitrary-precision staircase counters recompute the dimension and must match
both each other and the saved quotient and branch counts. This verifies a
reviewed solver's finished basis export rather than proving ideal membership
from a leading ideal alone.

Only after all four branches pass does the script emit the total. That sum must
satisfy the certified lower bound of 45,083,592 and be divisible by 12 (from
the free full-board palette and reflection action), with no division by 12 or
extra factor of 6 applied. Missing, timed-out, partial, or errored branches
stay unknown; an explicit zero requires the same completed-basis and
two-counter verification.

Example invocation (replacing the four placeholder paths with actual completed
backend result JSONs):

```sh
python experiments/exact_sign_branch_aggregate.py \
  experiments/result_branch0.json experiments/result_branch1.json \
  experiments/result_branch2.json experiments/result_branch3.json \
  --output experiments/fresh_four_branch_total_audit.json
```

The output path must not already exist. On failure, the script exits with code
1, status `INCOMPLETE_OR_INVALID`, and a null full count. A passing run writes
`COMPLETE_FOUR_BRANCH_TOTAL` with the exact decimal sum and per-branch artifact
hashes. Neither status is inferred simply because a basis file exists or a
leading export claims completion.

## Validation and metadata correction

`exact_sign_branch_aggregate_check.py` passes 85 tests. These cover all eight
frozen input scopes, tampered IDs/dimensions/maps/factors/restrictions/hashes,
a fixed-prefix input disguised as a full branch, malformed process/log/basis
records, missing and duplicate branches, lower-bound and symmetry failures, and
rejection of marked synthetic records by the production entry point. Both
integer counters also count a small 97-variable monomial fixture of dimension
6 (a software fixture, not a branch basis).

Positive terminal and aggregation test cases use in-memory synthetic values to
test code paths only and never represent real branch counts.
`exact_sign_branch_aggregate_check_results.json` records `PASS_TESTS_ONLY`,
zero completed branches, null unrestricted count, and zero solver runs.

Review caught one metadata bug: branch preparation wrote
`standard_basis_complete=False`, while the shared backend only updated
`basis_complete` on completion. The parent fixed the shared completion code to
update both flags before any full branch run, and the aggregator rejects any
explicitly false completion flag. The earlier pre-fix unbranched full run is
audited separately with its original metadata preserved and is not fed into
this four-branch aggregator.

## Affine-elimination extension checks

The separate mathematical audit `exact_algorithms_branch_elimination_review.json`
verified all 8 new inputs, 1,444 source-polynomial images, 388 ordinary
field-domain identities, 800 original-color forms, and 322 known-board
round-trips. The adapter audit `exact_algorithms_eliminated_adapter_review.json`
verified all 8 CLI preparations and rejected 25 invalid Python scopes and 4
invalid CLI flag combinations. Both are independent reviews by another agent,
not solver runs by this aggregator.

The extension test suite `exact_sign_branch_elimination_aggregate_check.py`
adds 199 checks, 256 mocked combinations choosing one representation per
branch, and 24 cross-representation duplicate-ID rejections, plus parser and
two-counter checks on small monomial fixtures with 93 through 97 variables. The
original 85-check suite still passes. Mocked records stay in memory, and the
production entry point rejects synthetic records.

Four real 81-cell-prefix specializations run by the other agent finished with
raw dimensions 6, 0, 0, 0 and `258-branch_id` generators (from fixing 81
original cells). This auditor rejects all four by their input hashes so those
three zeros can never be mistaken for unrestricted branch counts. Their results
and the two review hashes are logged in
`exact_sign_branch_elimination_aggregate_check_results.json`, marked
`PASS_TESTS_ONLY` with zero completed unrestricted branches.

## A single terminal branch

Passing `--terminal` audits a single backend result without summing a total:

```sh
python experiments/exact_sign_branch_aggregate.py --terminal \
  experiments/exact_msolve_branch3_eliminated_minfill_byte_3g.json \
  --output experiments/fresh_branch3_terminal_audit.json
```

Run this only after both the backend and outer terminal JSONs exist. The same
frozen-scope, variable-count, executable/library, and exact-command checks
apply. A completed branch is recounted by both integer counters and must be
divisible by 6 (the lower bound and divisibility by 12 apply only to the full
four-branch sum). Incomplete, errored, or timed-out branches keep a null branch
count, and `--terminal` always leaves the full-count field null without
substituting zero or updating any aggregate.

The compact preflight must confirm an actual launch, the recorded memory and
time limits, the reviewed executable, and the required 512 MiB headroom. A
deferred 4 GiB attempt is tracked separately from a later 3 GiB launch, and
prepared or still-running processes fail the terminal check. The current
branch-3 run uses the affine-eliminated minimum-fill input (93 variables, 174
generators, 3 GiB preflight); no outcome is claimed while it runs.

`exact_sign_branch_terminal_check.py` passes 26 simulated terminal-gate tests
covering timeout/error/postprocessing states, partial exports, conflicting
process or preflight metadata, and unknown-count preservation. Runtime command
and library checks are mocked in these tests while reusing the unchanged
production checks. Temporary synthetic files are cleaned up, and the saved
record is `PASS_TESTS_ONLY` with no real branch count or solver run.
