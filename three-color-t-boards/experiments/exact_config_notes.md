# Deterministic preprocessing and decomposition configurations

We tested three distinct Ganak configurations on the original rephased CNF, keeping its 200-variable cell support (without rerunning the reduced or marginal encodings). Input hashes, flags, logs, resource stats, and exit statuses are saved in `exact_config_results.json`.

All runs used deterministic integer counting (`--prob 0`), a 512 MB cache, and negative-literal branching (`--polar 3`), with 20-second wall limits for binary checks and 60-second limits for prefix C and unrestricted ternary runs. Every process finished normally or at its timeout.

## Configurations and source findings

- **fast_pipeline:** Ganak's `--fast` preset, keeping its default Arjun, Puura, and tree-decomposition passes while shrinking CMS/oracle budget multipliers to 0.1 and backward support-check conflicts to 50.
- **structural:** gate detection and bounded variable elimination only, turning off SAT probing, backward checks, backbone discovery, model covering, autarky, and oracle passes. `--allindep 1` allows functional auxiliaries as optional support variables, with 50 TD iterations enabled.
- **td_only:** the existing projected formula with Arjun and Puura disabled and 50 TD iterations enabled.

Exact flags live in `exact_config_benchmark.py`. Note that passing `--arjun 0` also skips Puura, since Puura runs inside the Arjun pipeline (see [`run_arjun`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/main.cpp#L474) and [`--fast`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/main.cpp#L202)).

Letting auxiliaries join the support is valid here because every auxiliary is uniquely forced by the board cells, so full counting and projected counting match (this would not hold for arbitrary CNFs).

## Results

All three configurations returned the binary orbit count of **42**. Starting from 572 binary variables, `fast_pipeline` shrank the formula to 292 variables (6.619 CPU seconds) and `structural` shrank it to 382 variables (1.972 CPU seconds), while `td_only` finished in 0.117 CPU seconds. Preprocessing slowed this small instance down.

On prefix C:
- `fast_pipeline` returned **2** in 16.122 CPU seconds; Puura eliminated every clause and variable, leaving a factor of 2 from one free sampling variable.
- `structural` returned **2** in 40.634 CPU seconds after shrinking the formula to 2,623 variables and 98 support variables.
- `td_only` timed out after 17.733 CPU seconds within its 60-second wall cap.

Because these ran concurrently, none of them show a speedup over the earlier 16.28-CPU-second baseline on prefix C.

All three unrestricted ternary runs timed out without a count (`exact_count: null`, never zero):

- `fast_pipeline` spent 31.764 CPU seconds stuck inside Puura's backbone SAT pass and never reached counting.
- `structural` finished preprocessing in 3.65 CPU seconds, cutting 13,543 variables down to **9,802** (197 support variables), then entered counting and ran 6 clause-database reductions over 29.406 total CPU seconds.
- `td_only` kept all 13,543 variables and 200 support variables, ran 6 clause-database reductions, and used 33.990 CPU seconds.

None of the three configurations delivered a clear speedup or finished the unrestricted count.

## Why enabling TD gave no guidance

This Ganak release hard-codes `td_max_edges = 70000` with no CLI override ([counter_config.hpp](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter_config.hpp#L115), [counter.cpp](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L579)). The structurally reduced full formula builds a 550,181-edge primal graph, and contraction of the unreduced projected formula aborts at 7,000,001 edges (`100 * td_max_edges + 1`). Both skip tree decomposition before reaching density checks, so setting `--td 1` had no effect on the full runs.

On the binary `td_only` case, the projected graph is a complete graph on 25 variables, so every support variable gets the same TD distance and Ganak ignores it.

## Reproduction

```sh
python experiments/exact_config_benchmark.py
```

This regenerates only the phased binary and fixed-prefix formulas under `exact_config*`, reads the existing `exact_phase_ternary.cnf` untouched, and runs all three configurations. Source boards and attribution stay in the original certificate files.
