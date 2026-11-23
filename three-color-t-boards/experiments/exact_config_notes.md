# Deterministic preprocessing and decomposition configurations

Three materially different configurations were tested on the original
rephased CNF, retaining its 200-variable cell support. No reduced or marginal
encoding was rerun. The complete input hashes, argument lists, logs, resource
usage, and terminal statuses are in `exact_config_results.json`.

All runs used deterministic integer counting (`--prob 0`), a 512 MB cache,
and negative-literal decisions (`--polar 3`). Binary checks had 20-second
wall limits; prefix C and unrestricted ternary trials had 60-second limits.
Every process terminated normally or at its declared limit.

## Configurations and source findings

- **fast_pipeline:** Ganak's `--fast` preset, retaining its default Arjun,
  Puura, and tree-decomposition stages. The preset only reduces CMS/oracle
  budget multipliers to 0.1 and backward support-check conflicts to 50.
- **structural:** gate detection and bounded variable elimination, while
  disabling SAT-based probing, backward checks, backbone discovery, model
  covering, autarky, and oracle passes. `--allindep 1` permits functional
  auxiliaries as optional support variables; 50 TD iterations are allowed.
- **td_only:** the existing projected formula with Arjun and Puura disabled,
  but tree decomposition enabled with 50 iterations.

The exact flag lists are kept in `exact_config_benchmark.py`. The original
`--arjun 0` setting bypasses Puura as well: Puura is invoked inside the Arjun
pipeline. See [the release's `run_arjun` implementation](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/main.cpp#L474)
and [`--fast` definition](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/main.cpp#L202).

Allowing auxiliaries as optional support does not change the intended count
here: every auxiliary is uniquely determined by the board. Therefore ordinary
model counting and projection onto the cell variables count the same objects.
This justification would not apply automatically to an arbitrary CNF.

## Results

Every configuration returned binary orbit count **42**. The baseline binary
formula has 572 variables. Preprocessing reduced that to 292 variables in
the fast pipeline and 382 in the structural variant. Their total CPU times
were 6.619 and 1.972 seconds; TD-only used 0.117 seconds. Formula reduction did
not make this small validation instance faster.

For prefix C, the fast pipeline returned exact count **2** in 16.122 CPU
seconds. Puura eliminated every clause and variable, retaining a factor of
2 from one free sampling variable. The structural variant also returned
**2**, in 40.634 CPU seconds, after reducing the formula to 2,623 variables
and 98 support variables. TD-only timed out after using 17.733 CPU seconds
within its 60-second wall limit. These concurrent-run observations do not
demonstrate an improvement over the earlier 16.28-CPU-second prefix result.

All three unrestricted runs timed out without a count:

- The fast pipeline used 31.764 CPU seconds and remained in Puura's backbone
  SAT analysis. It did not reach the counting loop.
- Structural preprocessing finished in 3.65 CPU seconds, reducing 13,543
  variables to **9,802**, with 197 support variables. Counting then proceeded;
  the run used 29.406 CPU seconds overall and recorded six clause-database
  reductions.
- TD-only used 33.990 CPU seconds and also recorded six clause-database
  reductions. It retained the original 13,543 variables and 200-variable
  support.

No configuration established a major practical improvement or the unrestricted
exact count. A timeout is recorded as `exact_count: null`, never as zero.

## Why enabling TD did not supply guidance

The released counter has a hard `td_max_edges = 70000` setting, with no CLI
flag exposing it. The structurally preprocessed full formula produces a
550,181-edge graph, so TD is skipped before the later density/ratio checks.
The unchanged projected formula's contraction stops at 7,000,001 edges
(100 times the limit, plus one) and is likewise skipped. Thus simply changing
`--td 0` to `--td 1` did not enable decomposition on these full instances.
See [the fixed limit](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter_config.hpp#L115)
and [the contraction and skip logic](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L579).

On the binary TD-only case the projected graph is a complete graph on its
25 support variables. Ganak explicitly reports that every projected variable
has the same TD distance and ignores the resulting guidance.

## Reproduction

```sh
python experiments/exact_config_benchmark.py
```

The script regenerates only the phased baseline binary and fixed-prefix
inputs under `exact_config*`, then runs exactly these three configurations.
It reads the existing `exact_phase_ternary.cnf` unchanged. The source boards
and their attribution remain in the original certificate files.
