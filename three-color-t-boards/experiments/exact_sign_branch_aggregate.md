# Strict aggregation of the four linear sign branches

`exact_sign_branch_aggregate.py` accepts one completed backend result for each
branch ID 0, 1, 2 and 3, and audits all retained artifacts before summing.
No unrestricted branch count has completed as part of this work; the total
remains unknown. The checker starts no solver.

The sixteen frozen inputs in two reviewed manifests are supported:

- `exact_f3_sign_branches_manifest.json`, hash
  `9ecb49f828699a3966c0349bddb4bc4f57cc163b65ba1855770357bf2e39d2c7`;
- `exact_f3_branch_elimination_manifest.json`, hash
  `91e25ac8803be65a12998e344060e3e48778e499722f30aaf7b5a663f8b2eaa0`.

Natural/minimum-fill orders and uneliminated/affine-eliminated forms are
alternative representations of each branch. Submitting two for the same ID
is an error, including when their dimensions agree. The elimination manifest
must retain the pinned original partition as its source. Other representations
remain unsupported.

Every accepted input must be byte-identical to its reviewed source and have
canonical variable names and characteristic 3. An uneliminated branch has
97 variables and `179+branch_id` generators. An affine-eliminated branch has
`n=96-branch_id` variables and `177-branch_id` generators. The basis parser,
leading-export checks and both integer counters use this checked variable
count. The original-color reconstruction, affine constants, pivot list and
variable maps are compared with the pinned representation metadata.

No original prefix is fixed. Both independent variables remain: offset at
index `n-2` and sign at `n-1` (95 and 96 in the uneliminated case). In an
eliminated representation a canonical color can have a constant term, so the
original-color reconstruction can include a term linear in the sign as well
as bilinear terms. The exact model metadata retains those terms. Factors of
three and two are already present in the quotient dimension, so divisor and
multiplier are one. Each full branch dimension must be divisible by six.

Result acceptance requires `COMPLETE`, integer return code zero, a completed
basis flag, required unique export attestation, and no contradictory completion
flags or backend errors. The actual log must contain exactly one anchored
`MSOLVE_PRIME_GB_EXPORT_COMPLETE` line and no failure diagnostics. The actual
command must select ordinary g1 export, exact LA2, one thread, reduced basis
and the exact input and basis paths. Only reviewed executable hashes from
builds seven and eight are accepted, with current executable and recorded
local-library bytes checked. If an outer-process result exists, it must also
attest a normal completed return, without timeout.

The basis file's hash, complete header, variable order, field, monomial order
and list are parsed strictly. Its leading-ideal JSON must match that parse and
its input/executable provenance exactly. Both existing Python arbitrary-precision
staircase algorithms independently recompute the dimension. Both must agree
with the recorded quotient and branch count. This checks a reviewed exact
solver's completed basis output; it does not construct an independent
Gröbner proof from a leading-ideal-only export.

The final sum is emitted only after four such audits. It must satisfy the
certified lower bound 45,083,592 and divisibility by 12 from the free full-board
palette/reflection action. No division by 12 or extra factor of six is applied.
Missing, timed-out, partial or error results remain unknown. An explicit zero
is acceptable only after the same completed-basis and two-counter checks.

Example invocation, replacing all four illustrative paths with actual complete
backend result JSONs:

```sh
python experiments/exact_sign_branch_aggregate.py \
  experiments/result_branch0.json experiments/result_branch1.json \
  experiments/result_branch2.json experiments/result_branch3.json \
  --output experiments/fresh_four_branch_total_audit.json
```

The output path must be fresh. Failure exits with code 1, status
`INCOMPLETE_OR_INVALID` and a null full-count field. Success would have status
`COMPLETE_FOUR_BRANCH_TOTAL` with the exact decimal sum and per-branch artifact
hashes. Neither status is inferred from the mere existence of a basis or a
self-reported leading-export completion flag.

## Validation and metadata correction

`exact_sign_branch_aggregate_check.py` passes 85 recorded checks. They include
all eight real frozen input scopes; altered IDs, dimensions, maps, factors,
restrictions and hashes; a known fixed-prefix input masquerading as a full
branch; malformed process/log/basis records; missing and duplicate branches;
lower-bound and symmetry failures; and explicit rejection of marked synthetic
records by the production entry point. Both integer algorithms also count a
small 97-variable monomial fixture with dimension six. That fixture is not a
branch basis.

Positive terminal and aggregation gate cases use explicitly artificial
in-memory values. They establish software behavior only, never branch counts.
`exact_sign_branch_aggregate_check_results.json` records
`PASS_TESTS_ONLY`, zero actual completed branches, null unrestricted count and
zero solver processes.

Review found that branch preparation supplied `standard_basis_complete=False`
but the common backend formerly updated only `basis_complete` on completion.
The parent fixed the common completion metadata to update both flags before
any full branch solve. This aggregator rejects an explicitly false completion
flag. The already running pre-fix full unbranched trial is handled by its own
terminal audit, using its actual export and preserving the original metadata;
it is not an input to this four-branch aggregator.


## Affine-elimination extension checks

The independent mathematical review is
`exact_algorithms_branch_elimination_review.json`: all eight new inputs,
1,444 source-polynomial images, 388 ordinary field-domain identities,
800 original-color forms and 322 known-board roundtrips were checked. The
separate adapter review, `exact_algorithms_eliminated_adapter_review.json`,
checks all eight actual CLI preparations and rejects 25 invalid Python scopes
and four invalid CLI combinations. Those are the other agent's independent
reviews, not solver runs performed by the aggregation auditor.

The extension checker `exact_sign_branch_elimination_aggregate_check.py`
adds 199 recorded checks, 256 explicitly mocked choices of one representation
per branch, and 24 cross-representation duplicate-ID rejection cases. It also
checks parsing and both integer counters on small monomial fixtures with
93 through 97 variables. The original 85-check regression still passes.
Mocked completion data remain in memory only, and production auditing rejects
all explicitly synthetic records.

The other agent's four actual 81-cell-prefix specializations completed with
raw dimensions 6, 0, 0, 0. Their files have `258-branch_id` generators, since
81 original-color fixes were added. This auditor independently rejects all
four by their actual input bytes/hash; those three zeros cannot be used as
unrestricted branch counts. Their terminal results and the two independent
model/adapter review hashes are recorded as coordination evidence in
`exact_sign_branch_elimination_aggregate_check_results.json`, which is marked
`PASS_TESTS_ONLY` and still reports zero completed unrestricted branch counts.


## A single terminal branch

The optional `--terminal` mode audits exactly one backend result without
aggregating a full total:

```sh
python experiments/exact_sign_branch_aggregate.py --terminal \
  experiments/exact_msolve_branch3_eliminated_minfill_byte_3g.json \
  --output experiments/fresh_branch3_terminal_audit.json
```

Run this only after the backend and outer terminal JSONs exist. The same
frozen scope, dynamic variable count, executable/library and exact-command
checks apply. A complete branch is recounted by both integer algorithms and
must be divisible by six. It is not subjected to the full-count lower bound
or divisibility by twelve; those conditions belong to the sum of all four
branches. An incomplete/error/timeout branch retains a null branch count.
The returned full-count field is always null in this mode, even for a
completed branch. It never substitutes zero or updates the aggregate.

The compact preflight must attest an actual launch, the recorded memory and
time limits, the reviewed executable and the required 512-MiB headroom.
A deferred 4-GiB attempt is distinct from a later actual 3-GiB launch. Prepared
or running processes cannot pass the terminal check. The current branch-3
trial is the affine-eliminated minimum-fill input with 93 variables and
174 generators; its actual preflight selected 3 GiB. No terminal outcome is
claimed while it runs.

`exact_sign_branch_terminal_check.py` passes 26 simulated terminal-gate tests,
including timeout/error/postprocessing states, partial exports, conflicting
process/preflight metadata and unknown-count preservation. Runtime command
and library checks are explicitly mocked in these tests; they reuse the
unchanged production checks exercised by completed-result auditing. Temporary
synthetic records are removed. The saved result is `PASS_TESTS_ONLY`, with no
verified branch count or solver process.
