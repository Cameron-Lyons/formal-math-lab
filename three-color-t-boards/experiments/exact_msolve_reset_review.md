# Existing eighth-build reset option

**Finding: `-u1` and `-u5` do not enable table reclamation on the ordinary
F3 g1/g2 path in the frozen eighth executable.** No full trial using those
flags is justified as a memory experiment on this executable alone.

The review is pinned to executable
`63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`.
No solver source, backend flag or build was changed, and no unrestricted
board model was run.

## Actual call path

`main.c:302` parses `-u`, and `io.c:1263` stores a positive interval in
`md->reset_ht`; zero selects the sentinel 2^31-1 and is printed as OFF.
The setting is displayed in the initial metadata and enables an `rht` timing
line in the final statistics.

The only source invocation of `reset_hash_table` is `modular.c:459`, inside
`f4sat_trace_application_test_phase`, where it runs when
`round % st->reset_ht == 0`. This is a saturation/tracing path excluded by
the eighth build's guards. It is not the ordinary F4 loop.

The accepted prime-field export path calls `core_gba` from
`msolve.c:1670`; the guarded `core_gba` calls `core_f4`. The latter's loop in
`f4.c:673` calls preprocessing, new-element computation and basis update,
then final interreduction. It has no reset invocation or interval test.
A complete search of C/header sources finds only the definition at
`hash.c:1668` and the saturation-path invocation above. No source-level
indirection calls it on the ordinary route.

Thus an enabled interval in the printed options is not evidence that a
reset occurred. The native comparisons below confirm unchanged retained
exports and allocation/promotion events; their rounded zero reset timings
alone would not prove the call-path claim.

## What the existing reset helper would do if called

The helper retains both `esz` and `hsz`. It allocates a new pointer array
and contiguous exponent slab at the **same capacity** while holding the old
ones, then clears/reuses the existing metadata and bucket arrays. It resets
the load to one, reinserts all terms of each stored polynomial with
`bs->red[i] < 2`, and reinserts each pending pair's LCM, rewriting those IDs.
Only after reinsertion does it free the old exponent slab and pointer array.

Consequently it does not immediately shrink allocated table capacity. During
the reset it needs the extra same-capacity exponent slab and pointer array;
under an address-space limit that transient allocation matters even before
all new pages are resident. Existing failure handling prints errors but is
not the newer checked reserve mechanism. It cannot safely be assumed to
rescue a table already near the process limit.

Reinsertion can discard unreferenced IDs, including obsolete LCMs generated
before pair criteria discarded them. A smaller load could delay later
capacity growth if the helper were integrated into the ordinary path and
if enough such IDs existed. There is no automatic bound on future capacity:
newly retained polynomial terms and pairs can continue to grow. In particular,
the ordinary update code marks redundant polynomials with `red=1`, and the
helper's `<2` condition keeps their supports too. It is not a sweep retaining
only the current minimal leading-monomial basis.

These are source semantics, not measured memory savings. No reset was
instrumented or newly wired into an ordinary computation in this review.

## Bounded native checks

`exact_msolve_reset_review.py` preserves 18 terminal tiny runs under
`exact_msolve_reset_review_runs`: two existing four-variable F3 fixtures and
the existing 19-variable nine-row six-completion fiber, each with g1/g2 and
`-u0`, `-u1`, `-u5`. Each child had a 15-second wall limit and 2-GiB
address-space cap. All completed normally with one export marker and no
error diagnostic.

For each fixture/export mode, all three basis files are byte-identical.
Both independent integer staircase counters verify the g1 dimensions:
9, 10 and 6 respectively. The latter is a known fixed-prefix count, not a
new unrestricted result. The allocation/promotion diagnostic sequences are
identical for every interval. Positive intervals are advertised correctly,
and their printed reset time is 0.00 seconds. No RSS improvement is claimed.

The source hashes, exact commands, complete outputs and timings are recorded
in `exact_msolve_reset_review_results.json`, status
`PASS_NO_ORDINARY_RESET_CALL`. No further reset-option variants were tested.
