# Natural-F3 model with Singular

The independently checked, translated minimum-fill model was also tried with
Singular's `slimgb` algorithm. The unrestricted run exhausted its 3 GiB
address-space allowance after 41.8334 seconds (41.0138 child CPU seconds).
Singular exited with code 14 and `Singular error: no more memory`. It printed
`GB_STARTED` but no basis-completion marker, leading ideal, or count.

A separate `std` trial on the same input also exhausted its 3 GiB allowance:
66.6938 seconds elapsed, 64.7878 child CPU seconds, exit code 14 and the same
memory diagnostic. Neither 180-second wall limit expired. Both runs are
terminal and have no basis or count.

This is a terminal failed calculation, not a zero count or a partial count.
The input is the same 96-variable, 176-generator, ordinary F3 ideal used by
the minimum-fill msolve trials. It retains the independent apex-color factor;
its quotient dimension, if evaluated, would already be the full labeled count.

`exact_native_singular.py` reads frozen `.ms` inputs, verifies their hashes and
grammar, and places the unchanged polynomial body in a Singular `dp` ring.
It supplies this definition to the existing `exact_algebra_backend.py` runner
within its own process. Neither the existing backend nor the frozen inputs
are modified. The adapter adds normal-exit, unique ordered marker, and exact
three-counter agreement requirements for accepting completed results.

Both `std` and `slimgb` reproduced the known nine-row-prefix count **6**, with
the Hilbert calculation and two independent integer monomial counters agreeing.
Their child CPU times were 1.01204 and 0.498581 seconds, respectively. These
are fixed-prefix validation cases, not unrestricted results.

Artifacts:

- `exact_native_singular_six_std.*` and `exact_native_singular_six_slimgb.*`:
  scripts, complete leading ideals, logs, metadata, and count checks.
- `exact_native_singular_adapter_audit.json`: exact polynomial-body roundtrips
  for both frozen inputs and 24 malformed-completion rejection checks.
- `exact_native_singular_full_slimgb_3g.*`: unrestricted script, terminal log,
  metadata, and memory preflight (4117 MiB available; 3584 MiB required).
- `exact_native_singular_full_std_3g.*`: the separate `std` trial and its
  preflight (4764 MiB available; 3584 MiB required).

The full trial had a 180-second wall limit, which did not expire. Input SHA-256:
`b73bf1f74eb55a2f7e5d2663471021bc8fa3e3250f208d955d8d97bdfa9190bd`.
The metadata records the actual Singular executable, script, adapter, and
existing backend hashes. Fresh output names are required for reproduction.
