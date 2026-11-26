# Existing eighth-build reset option

**Finding: `-u1` and `-u5` do not trigger hash-table reclamation on the ordinary F3 `-g 1` / `-g 2` path in the frozen eighth executable.** Running a full trial with those flags would not test memory reclamation on this binary.

This review inspects executable SHA-256 `63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`. No solver source, backend flag, or build was changed, and no unrestricted board model was run.

## Actual call path

`main.c:302` parses `-u`, and `io.c:1263` stores any positive interval in `md->reset_ht` (zero maps to the sentinel `2^31 - 1` and prints as `OFF`). The option appears in the startup banner and adds an `rht` timing line to the final summary.

Across all C and header files, `reset_hash_table` is defined at `hash.c:1668` and called in only one place: `modular.c:459`, inside `f4sat_trace_application_test_phase` when `round % st->reset_ht == 0`. That saturation/tracing path is blocked by the eighth build's scope guards and is never reached by the ordinary F4 loop.

Instead, prime-field basis export runs `msolve.c:1670` (`core_gba`) into `core_f4`. Its main loop (`f4.c:673`) runs symbolic preprocessing, new-element computation, basis update, and final interreduction, with no reset call or interval check anywhere (direct or indirect). Printing an enabled interval in the banner therefore does not mean resets occur.

## What `reset_hash_table` would do if called

Even if wired into the ordinary loop, `reset_hash_table` does not shrink table capacity:

- It keeps both `esz` and `hsz`, allocating a second same-capacity pointer array and exponent slab while the old ones are still live.
- It clears and reuses metadata and buckets, resets load to 1, and reinserts every stored polynomial with `bs->red[i] < 2` plus every pending pair's LCM (renumbering their IDs).
- Only after reinsertion does it free the old exponent slab and pointer array.

Under an address-space cap, that transient same-capacity double allocation matters even before new pages are touched, and its legacy error path lacks the newer checked reserve guards. It cannot safely rescue a process already near its memory cap.

Reinsertion could drop dead IDs (such as obsolete LCMs pruned by pair criteria) and delay later growth if enough unused IDs accumulated. Still, ordinary updates mark redundant basis elements with `red = 1`, which satisfies `red < 2` and keeps their supports in the table anyway, so it is not a minimal-basis sweep and puts no cap on future growth. These are source-level facts, not measured memory tests; no reset path was newly enabled here.

## Bounded native checks

`exact_msolve_reset_review.py` saves 18 tiny runs in `exact_msolve_reset_review_runs`: two 4-variable F3 fixtures plus the 19-variable nine-row six-completion fiber, each run with `-g 1` and `-g 2` across `-u0`, `-u1`, and `-u5` under a 15-second wall cap and 2-GiB address-space cap. All 18 finished normally with one export marker and no error diagnostics.

For each fixture and export mode, all three `-u` settings produced byte-identical bases and identical allocation/promotion diagnostic logs. Both independent integer staircase counters confirmed the `-g 1` quotient dimensions: 9, 10, and 6 (the last is the known fixed-prefix count, not an unrestricted result). Positive `-u` values print in the options banner with 0.00 seconds of reset time. No RSS saving is claimed.

Source hashes, commands, outputs, and timings are saved in `exact_msolve_reset_review_results.json` with status `PASS_NO_ORDINARY_RESET_CALL`.
