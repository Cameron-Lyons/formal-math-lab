# Prime-characteristic backend results

Including all 80 nonconstant moments made a known fixed-prefix fiber much faster to solve. The unrestricted ternary count is still unknown: both full characteristic-29 runs hit the 2 GiB address-space cap before finishing a basis.

## Exact model

`exact_prime_fourier.py` rebuilds the 81 geometric placements from scratch and sums integer multiplicities before reducing coefficients modulo a prime `p ≡ 2 (mod 3)`. The domain equations are `x_i^3 - 1`, and the script can emit either 40 Frobenius representatives or all 80 nonconstant moments. It does not reuse the characteristic-2 reduced export.

For unrestricted boards, every coefficient lies in `F29`. After scalar extension to `F29²`, the quotient dimension over `F29` equals the full labeled-board count, with no field-degree or symmetry multiplier. Fixed prefixes work over `F29²` with `a² + a + 1 = 0`, representing colors by `1`, `a`, and `-a - 1`.

`exact_parity_math_prime.md` proves this for general primes. Fourier inversion forces every one of the 81 pattern counts to be `1 (mod p)`; since counts are nonnegative and sum to 81, each must equal 1 (so `p` does not need to exceed 81). Characteristic 29 is also large enough that the one-role marginals, which are congruent to 27, must equal 27 exactly.

Generator checks passed at primes 5, 29, and 83, covering direct transforms of random boards, fixed-prefix specializations, known witnesses, invalid-board rejection, and Frobenius partners (`exact_prime_fourier_checks.json`). Backend checks also confirmed dimension 3 for a cubic domain, dimension 6 for three roots summing to zero, and dimension 1 for a `F29²` color-2 specialization.

The backend accepts `prime:29` (40 moments) and `prime-all:29` (all 80 moments). This generator requires complete-row prefixes. It builds all free cubic domains on its own and checks the characteristic, moment counts, and domain/variable totals. The full paired model has 100 variables and 140 generators; the full all-moment model has 100 variables and 180 generators. Input generation, script execution, and leading-ideal completion are tracked separately from completed counts.

## Fixed nine-row comparison

Both fibers leave 19 free cells. On every completed run, Singular's arbitrary-precision Hilbert sum matches both independent Python standard-monomial counters. Each result JSON stores the exact prefix used.

| Fiber | Characteristic / moments / algorithm | Result | Singular CPU seconds | Backend wall seconds |
| --- | --- | --- | ---: | ---: |
| One completion | 2 / 40 / std | exact 1 | 7.1931 | 9.0854 |
| Six completions | 2 / 40 / std | exact 6 | 18.5431 | 19.9193 |
| One completion | 29 / 40 / std | basis timeout, no count | 68.6263 | 90.1691 |
| Six completions | 29 / 40 / std | basis timeout, no count | 62.9867 | 90.1076 |
| Six completions | 29 / 80 / std | exact 6 | 0.878783 | 1.394316 |
| Six completions | 29 / 80 / slimgb | exact 6 | 0.282282 | 0.499472 |

The paired fixed-prefix models had 58 nonzero generators, and the all-moment model had 97. The finished all-moment `std` basis had 24 elements and Krull dimension 0. Timeouts do not give exact runtime ratios, and wall time is kept separate from process CPU time.

These runs back up the idea that supplying Frobenius partners directly helps the solver: in characteristic 29, deriving an omitted partner takes a 29th power instead of simple squaring as in characteristic 2. Still, speed on a fixed fiber does not predict scalability on the unrestricted problem.

Singular describes [`slimgb`](https://www.singular.uni-kl.de/web/docs/tutor-slim-groebner-bases-b7ee1d0d.html) as an algorithm aimed at keeping intermediate polynomials short (without guaranteeing lower memory on this input). The `F29²` fiber check verified that `slimgb` supports our coefficient field, global `dp` order, and `redSB` option.

To reproduce the `std` fiber run:

```sh
python experiments/exact_algebra_backend.py --model prime-all:29 --prefix 100011101011000101010011112112211212021201221022121202020220010222002102100022222 --output experiments/exact_algebra_backend_prime29_all_prefix_six --algorithm std --timeout 90 --memory-mb 2048
```

For `slimgb`, change only `--algorithm slimgb` and append `_slimgb` to the output prefix. For the 40-moment baseline, switch to `--model prime:29`.

## Full unrestricted trials

Both full trials ran on the same fresh `F29` ideal: all 100 cubic domains and all 80 nonconstant moments, with no fixed prefix or normalization, under `dp` order and `option(redSB)`. Any Singular error invalidates the run even if Singular prints a number later. Neither run produced a leading ideal.

| Algorithm | Terminal status | Failure | CPU seconds | Backend wall seconds |
| --- | --- | --- | ---: | ---: |
| std | BACKEND_ERROR; exit 14 | memory exhaustion | 39.830931 | 45.381755 |
| slimgb | BACKEND_ERROR; exit 14 | memory exhaustion | 34.386272 | 41.318538 |

Each Singular process ran with a 90-second wall limit and a 2147483648-byte address-space cap. Both died early with `Singular error: no more memory`. CPU times come from OS process counters. Neither run produced a basis, leading-ideal export, quotient dimension, or board count.

The `std` command:

```sh
python experiments/exact_algebra_backend.py --model prime-all:29 --output experiments/exact_algebra_backend_full_prime29_all --algorithm std --timeout 90 --memory-mb 2048
```

The `slimgb` command also wrapped the outer Python and counting process:

```sh
python experiments/exact_algebra_backend_guarded.py --output experiments/exact_algebra_backend_full_prime29_all_slimgb --outer-seconds 180 --outer-memory-mb 2048 -- --model prime-all:29 --algorithm slimgb --timeout 90 --memory-mb 2048
```

The outer guard finished cleanly after 41.651144 wall seconds after the backend reported memory exhaustion, so Python monomial counting never started. Its `.outer.json` records total process-tree CPU separately (34.560397 seconds), which differs from Singular-only CPU. The wrapper adds a wall and memory limit around postprocessing so counting cannot hang after Singular finishes.

Canonical geometry input: `exact_algebra_backend_full_prime29_all.model.json`, SHA256 `62fe4a4658fed394165eab3353f800c2cd22a446963dd9a6b4b4cd9aef6ed6db`.

Executed `std` script SHA256: `268e1453615d9724bf42dd38802c6a1a970efbe2826805d649df1712f27afbfc`.

Executed `slimgb` script SHA256: `12fbf974c6df0d8499348955dc14108e56294fd21c5f3194d713f40560589a38`.

`exact_algebra_backend_full_prime29_algorithm_comparison.json` confirms the two scripts differ only by replacing `std(I)` with `slimgb(I)`. Each run keeps its `.sing`, `.log`, and `.json` files. The memory cap stayed at 2 GiB throughout.

## Apex color normalization

A later run fixed only cell 0 to color 0 (root of unity `1`), passing `prefix=['0']` (`--prefix 0`). That kept the other 99 cells free, giving 99 cubic domains plus all 80 moments (179 generators) over `F29`, with no other fixed cells or extra constraints.

The backend prints raw extension counts without multiplying prime models. By cyclic color symmetry, a completed count for this apex-zero fiber would multiply by 3 to give the full labeled count, though the basis never finished so no count was produced.

The scope check is in `exact_algebra_backend_prime29_apex0_check.json`. To test normalization cheaply, we shifted the known nine-row six-completion prefix by subtracting its apex color mod 3; all three counters still returned raw exact 6 (unmultiplied) in 0.177926 Singular CPU seconds and 0.232240 wall seconds.

The apex-zero command:

```sh
python experiments/exact_algebra_backend_guarded.py --output experiments/exact_algebra_backend_prime29_apex0_slimgb --outer-seconds 180 --outer-memory-mb 2048 -- --model prime-all:29 --prefix 0 --algorithm slimgb --timeout 90 --memory-mb 2048
```

It ended with `BACKEND_ERROR`, Singular exit 14, and `Singular error: no more memory`, using 15.973701 Singular CPU seconds and 22.020047 backend wall seconds (outer wall time 22.129845 seconds). All three completion flags (standard basis, leading-ideal export, dimension) are false and no dimension is recorded.

Saved input SHA256: `cf45b7feaab85e5aee07394c3426e6e4eba41b9cc3922cb14e48c35f8abcfeb2`.

Executed script SHA256: `e8643cfd6a046f24f3ba32a23ffb1011f78abef06015e6ce0a178b6e8dbf4a5e`.

The `.model.json`, `.sing`, `.log`, `.json`, and `.outer.json` artifacts share the prefix `exact_algebra_backend_prime29_apex0_slimgb`. The metadata records count scope, fixed row/cell counts, fixed original cells, and separate completion flags for basis, export, and dimension. Writing a `RUNNING` status file before starting Singular prevents an outer kill from leaving a stale completed result. No top-two-row case was run here.
