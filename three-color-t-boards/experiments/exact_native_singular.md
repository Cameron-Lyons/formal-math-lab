# Natural-F3 model with Singular

We also ran Singular's `slimgb` algorithm on the independently checked,
translated minimum-fill model. The unrestricted run hit its 3 GiB memory limit
after 41.8334 seconds (41.0138 child CPU seconds). Singular exited with code 14
and printed `Singular error: no more memory`. It reached `GB_STARTED`, then
stopped without a basis-completion marker, leading ideal, or count.

A separate `std` run on the same input also hit the 3 GiB limit after 66.6938
seconds elapsed (64.7878 child CPU seconds), exiting with code 14 and the same
memory error. Neither run reached its 180-second wall limit. Both runs failed
before producing a basis or a count.

These are failed runs, so they give neither a zero count nor a partial count.
The input is the same 96-variable, 176-generator ordinary F3 ideal used in the
minimum-fill msolve trials. It keeps the independent apex-color factor, so its
quotient dimension would already equal the full labeled board count.

`exact_native_singular.py` reads the frozen `.ms` inputs, checks their hashes
and syntax, and puts the unchanged polynomials into a Singular `dp` ring. It
passes that ring to the existing `exact_algebra_backend.py` runner in the same
process, without changing the backend or the frozen inputs. To accept a finished
run, the adapter requires a normal exit, unique ordered completion markers, and
exact agreement across all three counters.

Both `std` and `slimgb` reproduced the known nine-row-prefix count of **6**,
with the Hilbert calculation and both independent integer monomial counters
agreeing. Their child CPU times were 1.01204 seconds for `std` and 0.498581
seconds for `slimgb`. These are fixed-prefix checks only, not unrestricted
results.

Artifacts:

- `exact_native_singular_six_std.*` and `exact_native_singular_six_slimgb.*`:
  scripts, complete leading ideals, logs, metadata, and count checks.
- `exact_native_singular_adapter_audit.json`: exact polynomial-body round-trips
  for both frozen inputs and 24 checks that reject malformed completions.
- `exact_native_singular_full_slimgb_3g.*`: unrestricted script, terminal log,
  metadata, and memory preflight (4117 MiB available; 3584 MiB required).
- `exact_native_singular_full_std_3g.*`: the separate `std` run and its
  preflight (4764 MiB available; 3584 MiB required).

The full run had a 180-second wall limit, which did not expire. Input SHA-256:
`b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`. The metadata
records the hashes of the Singular binary, script, adapter, and existing
backend. Use fresh output filenames when reproducing these runs.
