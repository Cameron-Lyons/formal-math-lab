# Exact algebra backend experiment

The unrestricted count is still unknown. We ran one full reduced-ideal computation, and it failed before finishing a standard basis (which does not mean zero solutions).

The local solver is Singular 4.4.1 (44105, 64-bit), extracted locally from the official Arch package `singular-4.4.1.p5-11` along with its missing dependencies, without touching system directories. `exact_algebra_backend_packages.json` stores the package versions, download URLs, and SHA256 checksums, and `exact_algebra_backend_setup.py` verifies every archive against that manifest before extracting.

## Model and exact count interpretation

The full Fourier model works in an ordinary polynomial ring over `F2`. Each ternary cell satisfies `x_i^3 + 1 = 0`. These are **not** Boolean variables; imposing `x_i^2 + x_i = 0` would break the encoding. Over `F4`, each cubic splits into three distinct nonzero roots, so the finite quotient is reduced and its vector-space dimension over `F4` equals the number of valid boards. Extending scalars from `F2` to `F4` keeps that dimension unchanged (counting `F2`-rational points would answer the wrong question).

The importer verifies these generator counts:

| Model | Variables | Generators |
| --- | ---: | ---: |
| Original ternary Fourier ideal | 100 | 100 cubic domains + 40 moments = 140 |
| Reduced ternary Fourier ideal | 96 | 96 cubic domains + 36 moments + 4 substituted pivot domains = 136 |
| Reduced binary Boolean ANF | 21 | 21 Boolean domains + 11 ANFs = 32 |

The 96 free cubic domains are generated directly from metadata rather than listed inside the reduced JSON's `remaining_equations` array. Full reduced runs fix no prefix or apex. `--normalize-apex` works only on the original ternary model, adding `x1 + 1` and recording a multiplier of 3; any other use is rejected before Singular starts.

Fixed ternary prefixes specialize over the field `F2[a]/(a^2 + a + 1)`, encoding colors 0, 1, 2 as `1`, `a`, `a + 1`. Singular's [algebraic-extension documentation](https://www.singular.uni-kl.de/Manual/latest/sing_408.htm) explains setting `minpoly` right after declaring this ring.

## Reliable integer counting

Singular's [`vdim`](https://www.singular.uni-kl.de/Manual/latest/sing_381.htm) returns a machine integer and assumes a standard basis, so we use it only as a quick check on tiny fixtures. Exact counts come from three independent paths:

1. Summing the coefficients of Singular's `bigintvec` second Hilbert series into a `bigint` accumulator, dropping its trailing metadata entry (see the [`hilb` documentation](https://www.singular.uni-kl.de/web/docs/reference-hilb-2eeb0fea.html)).
2. Counting standard monomials of the finished leading ideal with Python big integers in `exact_algebra_backend.py`.
3. Counting the same leading ideal with the separate implementation in `exact_standard_monomials.py`, which splits support components and branches on exponent intervals.

The script exports leading monomials before running `hilb`, and requires both a completed standard basis (attested by `attrib(G,"isSB")`) and a complete export. Zero polynomials are rejected before `leadexp`, so an all-zero exponent vector can only represent the constant monomial 1. Any Singular error message invalidates the run even if Singular keeps going and prints a count or exits 0; the test suite verifies this by triggering an undefined-procedure error followed by an otherwise normal basis and count.

If Hilbert computation times out after a complete leading-ideal export, agreement between the two Python monomial counters still gives the exact quotient dimension, reported as `COMPLETE_FROM_LEADING_IDEAL` while keeping the Hilbert timeout noted separately. The unrestricted trial never reached a completed basis.

## Validation results

Every completed count below matches across Singular's `bigint` Hilbert sum and both Python monomial counters. All rows are small fixtures or fixed-prefix fibers, not unrestricted ternary counts.

| Fixture | Exact quotient dimension |
| --- | ---: |
| One cubic root-of-unity domain | 3 |
| Two independent cubic domains | 9 |
| Two cubic domains with `x1+x2` | 3 |
| Cubic domain with `x1^2+x1+1` | 2 |
| Three cubic domains with `x1+x2+x3` | 6 |
| Reduced preceding fixture: two cubic domains and `(x1+x2)^3+1` | 6 |
| F4 cubic domain with `x1+a` | 1 |
| Unit ideal | 0 |
| Ten independent domains `x_i^100+1` | 100000000000000000000 |
| Known nine-row ternary prefix, first seed | 1 |
| Known nine-row ternary prefix, six-completion fiber | 6 |

The $10^{20}$ fixture exceeds 64-bit integers on purpose to test big-integer counting, so its nonradical characteristic-2 domains are harmless here. Both nine-row ternary fibers match earlier exhaustive row enumeration and last-row dynamic programming (`exact_lastrow_check.py` and its log). Each Singular run had 19 variables and 58 generators, taking 7.1931 and 18.5431 process CPU seconds (9.0854 and 19.9193 wall seconds). The exact 81-color prefixes are saved in `exact_algebra_backend_ternary_prefix_one.json` and `exact_algebra_backend_ternary_prefix_six.json`.

A 21-variable binary standard-basis run timed out at 90.0969 wall seconds (84.0456 CPU seconds, 2 GiB cap) without finishing, so the known binary count of 168 is not claimed as a Gröbner result here.

An earlier run on 100 independent cubic domains finished its basis and then timed out inside `hilb` after 60 seconds, which led us to export the leading ideal before calling `hilb`. Its exact dimension is $3^{100}$, which both Python counters evaluate directly, though that earlier saved run itself has no completed Hilbert output.

To run the small fixtures, import checks, normalization misuse tests, error-rejection test, and re-verification of saved fiber leading ideals:

```sh
python experiments/exact_algebra_backend_setup.py
python experiments/exact_algebra_backend_check.py
```

Add `--include-fibers` to recompute the two fixed-prefix bases (the script never launches an unrestricted run). Saved results are in `exact_algebra_backend_check.json`, and an independent re-check of all previously exported leading ideals is in `exact_algebra_backend_independent_validation.json`.

An independent audit (`exact_parity_math_backend_review.json`) also checked 300 fresh finite-box leading ideals, fully fixed valid and invalid ternary boards (dimensions 1 and 0), and synthetic Hilbert-timeout, incomplete-export, and error-diagnostic cases.

## The single unrestricted characteristic-two trial

The exact command was:

```sh
python experiments/exact_algebra_backend.py --model ternary-reduced --output experiments/exact_algebra_backend_full_reduced --algorithm std --timeout 90 --memory-mb 2048
```

This runs `std(I)` with `option(redSB)` over `F2` in `dp` order on 96 variables and 136 generators. The wrapper launches local `Singular -q`, feeds it the saved `.sing` script on stdin, points library lookup at the local extraction, sets `RLIMIT_AS` to 2147483648 bytes, enforces a 90-second wall timeout, and logs OS process CPU time separately.

Result:

| Item | Recorded result |
| --- | --- |
| Terminal status | `BACKEND_ERROR` |
| Failure | `Singular error: no more memory`, followed by wall timeout |
| Standard basis complete | false |
| Process CPU seconds | 62.811871 |
| Wall seconds | 90.358622 |
| Quotient dimension | not computed |

Memory exhaustion and the wall timeout are recorded separately, and CPU time comes from the OS rather than wall time. We ran no further unrestricted characteristic-2 Gröbner trials; later characteristic-29 trials are in `exact_algebra_backend_prime_results.md`.

Input JSON SHA256: `66e18148d574178bfdc09296635e43ebe327646beff90ab8c5a6d43e88729c78`.

Executed Singular script SHA256: `6ed1e7cbbbe034ed8ee23961bbed2332ef2be7185207bb4379e7bb815a32204e`.

The raw script, log, and metadata are `exact_algebra_backend_full_reduced.sing`, `.log`, and `.json`. Overall, the experiment confirms that the exact algebraic reduction imports and counts accurately on nontrivial fixed fibers, while bounded `std` over `F2` did not scale to the unrestricted board.
