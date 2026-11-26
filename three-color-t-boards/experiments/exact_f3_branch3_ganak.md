# Bounded full-label branch-3 GANAK probe

The single deterministic probe **timed out without an exact count**, so the count for branch 3 is still unknown. Although the timeout itself decides neither SAT nor UNSAT, branch 3 is already known to be nonempty because two valid boards in `exact_structure_gauge_rank.json` satisfy its equations (`UNKNOWN` existence fields in the JSON files only record that the solver did not decide it).

The CNF has 13,341 variables and 59,308 clauses: the existing parsimonious tree encoding with all 100 cells free, plus 21 direct one-hot clauses enforcing:

```
c0=c3,  c1=c6,  c2=c7,  c3!=c8.
```

These are the exact full-label branch-3 conditions for placements `P0 = (0, 1, 2, 3)` and `P3 = (3, 6, 7, 8)`. There is no prefix, palette breaking, reflection breaking, or projection support. Every auxiliary remains uniquely determined, so a full model count would equal the branch count directly (multiplier and divisor 1).

Reading the 21 appended clauses back from DIMACS and testing all 2,187 ternary assignments of cells `0, 1, 2, 3, 6, 7, 8` confirmed that exactly 54 assignments satisfy the local relation (a local truth-table check, not a board count). All base clauses stayed unchanged and no new variables were added.

A separate unsolved fixture appends the known six-completion 81-cell prefix, which contradicts branch 3 because it fixes `c0 = 1` and `c3 = 0`. The audit records the exact four conflicting clauses (those two unit literals, one equality clause, and one cell-3 one-hot exclusion), and the seven-cell truth table rejects the assignment directly, confirming a restricted count of 0 without needing another solver run. Those prefix units do not appear in the main CNF.

The Ganak binary matched SHA256 `e7a3c6a66377db349939ceb01c78783767fbca5a3ef3dad66cbc6cf11f2daf58`, and its help output verified all flags including single-thread mode. Command:

```
experiments/exact_count_tools/ganak --prob 0 --mode 0 \
  --arjun 0 --puura 0 --td 0 --threads 1 --maxcache 128 --appmct -1 \
  experiments/exact_f3_branch3_ganak.cnf
```

The worker ran with a 512 MiB address-space cap, a 60-second child wall limit, and a 90-second outer guard (available memory at launch was 2,477,596 KiB, above the 1,536 MiB threshold). The log confirms single-threaded exact counting over all 13,341 variables with approximate fallback disabled.

The child timed out after 60.180 wall seconds (27.038 CPU seconds) without printing a count. The wrapper killed and reaped it cleanly, exiting at 60.761 seconds (the wrapper's exit code 0 reflects clean cleanup, not solver completion). No solver process remains running.

Artifacts share the prefix `exact_f3_branch3_ganak` (runner, full CNF, audit JSON, raw log/status, outer log/status, help/version logs, and unsolved prefix CNF). Input SHA256: `142ee7f7007dbc9dc1698c6625ccf6c7156f608dfa9529ef380d29b53ded7629` (matching prepared source and executed files).

A broad log scan matched the word `ASSERTIONS` in Ganak's build banner. The [diagnostic review](exact_f3_branch3_ganak.diagnostic_review.json) confirms this is build metadata rather than a runtime assertion failure while leaving the raw status untouched; the terminal status stays **UNKNOWN_TIMEOUT** either way.

No packages were installed, no extra solver runs were launched, and no existing CNF generator or algebra backend was changed.
