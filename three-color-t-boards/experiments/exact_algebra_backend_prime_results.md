# Prime-characteristic backend results

Explicitly supplying all 80 nonconstant moments made a known fixed-prefix fiber substantially faster. The unrestricted count remains unknown: both authorized full characteristic-29 algorithms exhausted the 2 GiB address-space cap before completing a basis.

## Exact model

`exact_prime_fourier.py` rebuilds the 81 geometric placements and accumulates integer multiplicities before reducing coefficients modulo a prime `p ≡ 2 (mod 3)`. The ordinary polynomial domains are `x_i^3-1`. It supports either 40 Frobenius representatives or all 80 nonconstant moments. The characteristic-two reduced export is not reused.

For unrestricted boards all coefficients lie in F29. Its quotient dimension over F29 equals the full labeled-board count after scalar extension to F29². There is no field-degree or symmetry multiplier. Fixed prefixes use F29² with `a²+a+1=0` and colors represented by `1,a,-a-1`.

The general-prime proof is in `exact_parity_math_prime.md`. Fourier inversion gives each of the 81 pattern multiplicities congruent to 1 modulo p; their nonnegativity and total 81 force each to equal 1. Characteristic 29 is also large enough for the one-role marginals, congruent to 27, to be exactly 27. The prime does not need to exceed 81.

Generator checks passed at 5,29,83, including random-board direct transforms, fixed-prefix specializations, known witnesses, invalid-board rejection and Frobenius partners. See `exact_prime_fourier_checks.json`. Backend checks also establish cubic-domain dimension 3, three-root sum-zero dimension 6, and the genuine F29² color-2 specialization dimension 1.

The backend models are `prime:29` for 40 moments and `prime-all:29` for all 80. Complete-row prefixes are required by this generator. It independently generates all free cubic domains, asserts the characteristic and moment totals, and checks the domain/free-variable counts. Full paired input has 100 variables and 140 generators; full all-moment input has 100 variables and 180 generators. Fully specified input, script and leading-ideal completion are distinguished from completed counts.

## Fixed nine-row comparison

Both fibers have 19 free cells. Every completed count agrees between Singular's bigint Hilbert sum and the two independent Python standard-monomial counters. The exact prefixes are retained in each result JSON.

| Fiber | Characteristic / moments / algorithm | Result | Singular CPU seconds | Backend wall seconds |
| --- | --- | --- | ---: | ---: |
| One completion | 2 / 40 / std | exact 1 | 7.1931 | 9.0854 |
| Six completions | 2 / 40 / std | exact 6 | 18.5431 | 19.9193 |
| One completion | 29 / 40 / std | basis timeout, no count | 68.6263 | 90.1691 |
| Six completions | 29 / 40 / std | basis timeout, no count | 62.9867 | 90.1076 |
| Six completions | 29 / 80 / std | exact 6 | 0.878783 | 1.394316 |
| Six completions | 29 / 80 / slimgb | exact 6 | 0.282282 | 0.499472 |

The paired fixed-prefix models had 58 nonzero generators; the all-moment model had 97. The completed all-moment std basis had 24 elements and zero Krull dimension. A timeout is not an exact runtime comparison, and wall times are not substituted for process CPU measurements.

The all-moment result supports the specific hypothesis that explicitly supplying Frobenius partners helps this polynomial computation. In characteristic 29 an omitted partner follows by a 29th-power derivation, whereas in characteristic two it follows by squaring. This explains a plausible algorithmic obstacle; the finite-fiber benchmark does not establish unrestricted scalability.

Singular documents [`slimgb`](https://www.singular.uni-kl.de/web/docs/tutor-slim-groebner-bases-b7ee1d0d.html) as an algorithm designed to keep intermediate polynomials short. It is a targeted alternative, not a guarantee of reduced memory use on this instance. The actual F29² fiber validation established support for the coefficient field, global `dp` order and `redSB` setting used here.

To reproduce the successful std fiber:

```sh
python experiments/exact_algebra_backend.py --model prime-all:29 --prefix 100011101011000101010011112112211212021201221022121202020220010222002102100022222 --output experiments/exact_algebra_backend_prime29_all_prefix_six --algorithm std --timeout 90 --memory-mb 2048
```

The slimgb comparison changes only `--algorithm slimgb` and uses output suffix `_slimgb`. The baseline paired run uses model `prime:29`.

## Full unrestricted trials

Both full trials used the same fresh F29 ideal: all 100 cubic domains and all 80 nonconstant moments, no prefix and no normalization. The order was `dp` and `option(redSB)` was enabled. Every Singular error is rejected even if the interpreter later prints a number. Neither trial produced a completed leading ideal.

| Algorithm | Terminal status | Failure | CPU seconds | Backend wall seconds |
| --- | --- | --- | ---: | ---: |
| std | BACKEND_ERROR; exit 14 | memory exhaustion | 39.830931 | 45.381755 |
| slimgb | BACKEND_ERROR; exit 14 | memory exhaustion | 34.386272 | 41.318538 |

Each Singular process had a 90-second wall limit and a 2147483648-byte address-space limit. Both failed before reaching the wall limit, with the diagnostic `Singular error: no more memory`. The process CPU measurements are OS counters. There is no basis, leading export, quotient dimension, or unrestricted board count from either run.

The exact std command was:

```sh
python experiments/exact_algebra_backend.py --model prime-all:29 --output experiments/exact_algebra_backend_full_prime29_all --algorithm std --timeout 90 --memory-mb 2048
```

The slimgb command also guarded the outer Python/counting process:

```sh
python experiments/exact_algebra_backend_guarded.py --output experiments/exact_algebra_backend_full_prime29_all_slimgb --outer-seconds 180 --outer-memory-mb 2048 -- --model prime-all:29 --algorithm slimgb --timeout 90 --memory-mb 2048
```

The outer guard finished normally after 41.651144 wall seconds; the backend returned its memory-error status, and no Python monomial counting began. Its `.outer.json` separately records aggregate process-tree CPU (34.560397 seconds), which must not be confused with Singular-only CPU. The wrapper has a finite whole-process wall limit and address-space cap so future completed-basis postprocessing cannot run indefinitely outside the Singular timeout.

The canonical geometry input is `exact_algebra_backend_full_prime29_all.model.json` with SHA256 `62fe4a4658fed394165eab3353f800c2cd22a446963dd9a6b4b4cd9aef6ed6db`.

Executed std script SHA256: `268e1453615d9724bf42dd38802c6a1a970efbe2826805d649df1712f27afbfc`.

Executed slimgb script SHA256: `12fbf974c6df0d8499348955dc14108e56294fd21c5f3194d713f40560589a38`.

`exact_algebra_backend_full_prime29_algorithm_comparison.json` records that the script difference is exactly `std(I)` replaced by `slimgb(I)`. Each run retains its `.sing`, `.log`, and `.json` artifacts. The memory cap was never raised.

## Apex color normalization

One later trial fixed exactly original cell 0 to color 0, represented by the root of unity 1. The generator input was `prefix=['0']`; the backend argument was `--prefix 0`. It retained all other 99 original cells as free variables, giving 99 cubic domains plus all 80 moments, or 179 generators, over ordinary F29. No other prefix cells or normalization equations were imposed.

The backend reports raw extension counts and applies no multiplier to prime models. For this particular one-cell prefix the full labeled count would be three times a completed extension count, by global cyclic color permutation. Since the basis did not complete, no such count or product was computed.

The scope check is saved in `exact_algebra_backend_prime29_apex0_check.json`. As a cheap independent validation of normalization behavior, the known nine-row six-completion prefix was globally recolored by subtracting its apex color modulo 3. Its normalized prefix still returned raw exact 6 by all three count paths in 0.177926 Singular CPU seconds and 0.232240 wall seconds. This fixed nine-row count was not multiplied by three.

The single apex-only command was:

```sh
python experiments/exact_algebra_backend_guarded.py --output experiments/exact_algebra_backend_prime29_apex0_slimgb --outer-seconds 180 --outer-memory-mb 2048 -- --model prime-all:29 --prefix 0 --algorithm slimgb --timeout 90 --memory-mb 2048
```

It terminated with `BACKEND_ERROR`, Singular exit 14 and `Singular error: no more memory`: 15.973701 Singular CPU seconds and 22.020047 backend wall seconds. The outer process finished normally at 22.129845 wall seconds. The standard basis, leading-ideal export and dimension completion flags are all false, and no quotient dimension is present.

Saved input SHA256: `cf45b7feaab85e5aee07394c3426e6e4eba41b9cc3922cb14e48c35f8abcfeb2`.

Executed script SHA256: `e8643cfd6a046f24f3ba32a23ffb1011f78abef06015e6ce0a178b6e8dbf4a5e`.

The `.model.json`, `.sing`, `.log`, `.json`, and `.outer.json` files share prefix `exact_algebra_backend_prime29_apex0_slimgb`. New result metadata explicitly records count scope, fixed row/cell counts, fixed original cells, and separate standard-basis/export/dimension completion flags. A RUNNING record is written before launching Singular so an outer limit cannot leave a stale completed result. No top-two-row case was run.
