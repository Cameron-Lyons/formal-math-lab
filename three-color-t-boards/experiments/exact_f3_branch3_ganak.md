# Bounded full-label branch-3 GANAK probe

The single authorized deterministic probe **timed out without an exact
count**. Branch 3's count remains unknown. No SAT or UNSAT conclusion is
inferred from the timeout itself, but branch 3 is nonempty: two valid boards
in `exact_structure_gauge_rank.json` satisfy its conditions. The `UNKNOWN`
existence entries in the saved JSON files record only that no solver decided
the question.

The complete CNF has 13,341 variables and 59,308 clauses. It uses the existing
parsimonious tree encoding with all 100 original cells free, and appends only
21 direct one-hot clauses expressing

```
c0=c3,  c1=c6,  c2=c7,  c3!=c8.
```

These are exactly the full-label branch-3 conditions for placements
P0=(0,1,2,3) and P3=(3,6,7,8). There is no fixed prefix, palette normalization,
reflection normalization or projected support. Every auxiliary remains
functional, so a complete ordinary Boolean model count would equal the full
branch count, with multiplier and divisor one.

The actual clauses were read back from DIMACS and independently checked on
all 2,187 ternary assignments of cells 0,1,2,3,6,7,8. Exactly 54 satisfy the
intended local relation; this is not a board count. All base clauses are
retained unchanged and no new auxiliary variables are introduced.

A separate, unsolved check fixture appends the previously known six-completion
81-cell prefix. It is contradictory with this branch: that prefix fixes
c0=1 and c3=0. The audit records the exact four clauses consisting of those
two unit fixes, one equality implication and one cell-3 one-hot exclusion.
The seven-cell relation table independently rejects the fixed assignment.
This proves the expected prefix-restricted branch count zero without a second
solver invocation. These prefix units are absent from the main input.

The existing executable matched SHA256
`e7a3c6a66377db349939ceb01c78783767fbca5a3ef3dad66cbc6cf11f2daf58`.
Its local help confirmed every option, including one-thread support. The
count command was:

```
experiments/exact_count_tools/ganak --prob 0 --mode 0 \
  --arjun 0 --puura 0 --td 0 --threads 1 --maxcache 128 --appmct -1 \
  experiments/exact_f3_branch3_ganak.cnf
```

The worker enforced a 512 MiB address-space cap and 60-second child wall
limit, with a separate 90-second outer guard. Available memory immediately
before launch was 2,477,596 KiB, above the required 1,536 MiB. The log confirms
nonparallel counting over all 13,341 Boolean variables. Approximate fallback
was disabled.

The child ended by timeout after 60.180 wall seconds and 27.038 CPU seconds.
It emitted no exact count line. The wrapper killed and waited for it; the
outer handler completed after 60.761 seconds. The handler's exit zero is not
an exact counter completion. No solver remains running from this probe.

Artifacts share the prefix `exact_f3_branch3_ganak`: the Python runner, full
CNF, audit JSON, raw log and status JSON, outer log/status, help/version logs,
and unsolved known-prefix CNF. The input SHA256 is
`142ee7f7007dbc9dc1698c6625ccf6c7156f608dfa9529ef380d29b53ded7629`.
The prepared source and input hashes still match the executed files.

The raw worker's broad diagnostic scan also matched the word `ASSERTIONS` in
Ganak's compiler-configuration banner. The separate
[diagnostic review](exact_f3_branch3_ganak.diagnostic_review.json) identifies
this as metadata, not a runtime assertion failure; the raw status is preserved.
The terminal result remains **UNKNOWN_TIMEOUT** regardless of that harmless
match.

No package was installed, no additional decision/count run was made, and no
existing CNF generator or algebra backend was changed.
