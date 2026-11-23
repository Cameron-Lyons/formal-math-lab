# Exact algebra backend experiment

The unrestricted count is still unknown. One full reduced-ideal computation was attempted and did not complete a standard basis. Its failure must not be interpreted as zero solutions.

The local backend is Singular 4.4.1 (44105, 64 bit), extracted from the official Arch package `singular-4.4.1.p5-11` with its missing dependencies. No system packages were installed. `exact_algebra_backend_packages.json` records package versions, download URLs and SHA256 checksums. `exact_algebra_backend_setup.py` reuses that pinned manifest and validates every archive before local extraction.

## Model and exact count interpretation

The full Fourier model uses an ordinary polynomial ring over F2. Each ternary cell satisfies `x_i^3+1=0`; these are **not** Boolean variables, and adding `x_i^2+x_i` would destroy the model. Over F4 every cubic domain splits into three distinct nonzero roots. The resulting finite quotient is reduced; after scalar extension its vector-space dimension is the number of valid boards. Scalar extension preserves this dimension. Counting F2-rational points would be a different, incorrect task.

The importer checks these generator totals:

| Model | Variables | Generators |
| --- | ---: | ---: |
| Original ternary Fourier ideal | 100 | 100 cubic domains + 40 moments = 140 |
| Reduced ternary Fourier ideal | 96 | 96 cubic domains + 36 moments + 4 substituted pivot domains = 136 |
| Reduced binary Boolean ANF | 21 | 21 Boolean domains + 11 ANFs = 32 |

The 96 free cubic domains are generated explicitly; they are metadata rather than entries of the reduced JSON's `remaining_equations` array. Full reduced computations impose no prefix or apex restriction. The optional `--normalize-apex` flag is accepted only for the original ternary model, where it adds `x1+1` and records the justified multiplier 3. Unsupported uses are rejected before running Singular.

Fixed ternary prefixes are specialized over the genuine coefficient field `F2[a]/(a^2+a+1)`, with original colors 0, 1, 2 represented by `1`, `a`, `a+1`. Singular's [algebraic-extension documentation](https://www.singular.uni-kl.de/Manual/latest/sing_408.htm) explains setting `minpoly` immediately after declaring this ring.

## Reliable integer counting

Singular's [`vdim`](https://www.singular.uni-kl.de/Manual/latest/sing_381.htm) returns a machine integer and assumes a standard basis. It is used only as a diagnostic on tiny fixtures. Counts are obtained independently by:

1. Summing Singular's `bigintvec` second Hilbert-series coefficients with a `bigint` accumulator, excluding its final metadata entry. The current [`hilb` documentation](https://www.singular.uni-kl.de/web/docs/reference-hilb-2eeb0fea.html) specifies this vector representation.
2. Counting standard monomials of the completed leading ideal with Python integers in `exact_algebra_backend.py`.
3. Counting the same leading ideal with the independently implemented `exact_standard_monomials.py`, which factors support components and branches on exponent intervals.

The script exports leading monomials before computing the Hilbert series. A completed standard basis and complete export are required; `attrib(G,"isSB")` must attest that the basis is standard. Zero polynomials are rejected before `leadexp`, so the all-zero exponent vector can mean only the unit monomial. Every Singular error diagnostic invalidates a run even if the interpreter continues and later prints counts or exits successfully. The checker verifies this with an actual undefined-procedure error followed by otherwise successful basis/count output.

If Hilbert evaluation alone times out after a completed leading-ideal export, agreement between both independent monomial counters can still establish the exact quotient dimension; the runner reports `COMPLETE_FROM_LEADING_IDEAL` and retains the Hilbert timeout separately. No such completed basis was obtained in the unrestricted trial.

## Validation results

All completed counts below agree between Singular's bigint Hilbert sum and both Python monomial counters. These are fixtures or fixed-prefix fibers, not unrestricted ternary counts.

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

The `10^20` fixture explicitly exceeds 64-bit range. It tests dimension arithmetic, so its nonradical characteristic-two domains cause no problem. The ternary fibers agree with prior exhaustive row enumeration and terminal-row dynamic programming (`exact_lastrow_check.py` and its saved log). Their Singular runs used 19 variables and 58 generators, requiring respectively 7.1931 and 18.5431 process CPU seconds; wall times were 9.0854 and 19.9193 seconds. The exact 81-color prefix strings are recorded in `exact_algebra_backend_ternary_prefix_one.json` and `exact_algebra_backend_ternary_prefix_six.json`.

The binary 21-variable standard-basis trial timed out before completion: 90.0969 wall seconds, 84.0456 process CPU seconds, 2 GiB address-space cap. It produced no algebraic count. The known independent binary count 168 is not claimed as a completed Gröbner result.

An early test of 100 independent cubic domains completed its basis but then timed out in Hilbert computation after 60 seconds. That prompted exporting the leading ideal before calling `hilb`. Its dimension is mathematically `3^100`; the two Python counters handle this pure-power ideal directly. The saved early run itself lacks a completed Hilbert result.

Run the small fixtures, import checks, normalization misuse checks, actual-error rejection check, and independent verification of saved fiber leading ideals:

```sh
python experiments/exact_algebra_backend_setup.py
python experiments/exact_algebra_backend_check.py
```

Add `--include-fibers` to recompute the two fixed-prefix bases. No unrestricted computation is launched by the check script. The saved checks are `exact_algebra_backend_check.json`; a separate independent comparison of all previously exported leading ideals is `exact_algebra_backend_independent_validation.json`.

An independent review also checked 300 fresh finite-box leading ideals, fully fixed valid and invalid ternary boards (dimensions 1 and 0), and synthetic Hilbert-timeout, incomplete-export and diagnostic cases. Its saved audit is `exact_parity_math_backend_review.json`.

## The single unrestricted characteristic-two trial

The exact command was:

```sh
python experiments/exact_algebra_backend.py --model ternary-reduced --output experiments/exact_algebra_backend_full_reduced --algorithm std --timeout 90 --memory-mb 2048
```

It computes `std(I)` with `option(redSB)` in the ordinary F2 polynomial ring, degree reverse lexicographic order (`dp`), 96 variables and all 136 generators. The wrapper launches the locally extracted `Singular -q`, provides the saved `.sing` file's contents on standard input, sets `RLIMIT_AS` to 2147483648 bytes, and enforces a 90-second wall timeout. Library lookup is set to the local extraction. OS process CPU usage is recorded separately.

Result:

| Item | Recorded result |
| --- | --- |
| Terminal status | `BACKEND_ERROR` |
| Failure | `Singular error: no more memory`, followed by wall timeout |
| Standard basis complete | false |
| Process CPU seconds | 62.811871 |
| Wall seconds | 90.358622 |
| Quotient dimension | not computed |

The package memory diagnostic and wall timeout are separate facts; the CPU measurement is not inferred from wall time. No further unrestricted characteristic-two Gröbner trial was run. The later characteristic-29 experiments are recorded separately in `exact_algebra_backend_prime_results.md`.

Input JSON SHA256: `66e18148d574178bfdc09296635e43ebe327646beff90ab8c5a6d43e88729c78`.

Executed Singular script SHA256: `6ed1e7cbbbe034ed8ee23961bbed2332ef2be7185207bb4379e7bb815a32204e`.

Raw script, output and metadata are `exact_algebra_backend_full_reduced.sing`, `.log`, and `.json`. The experiment establishes that this exact algebraic reduction can be imported and counted correctly on nontrivial fixed fibers; this bounded `std` computation did not make the unrestricted count tractable.
