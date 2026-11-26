# Functional marginal constraints for exact counting

These experiments did not evaluate the unrestricted ternary count. `exact_marginal_cnf.py` extends `exact_count_cnf.py` (leaving that file untouched) by adding exact color-count cardinality constraints built from uniquely determined auxiliary variables.

In each of the four T roles (top, left, middle, right), every color appears 27 times across 81 distinct board cells (8 times across 16 cells for binary boards). Optional pair marginals also enforce that every ordered color pair appears 9 times across any two roles (4 times for binary boards).

Two count-preserving circuit encodings are supported:

- `--cardinality sequential`: defines each counter bit via `s[i,k] iff s[i-1,k] OR (s[i-1,k-1] AND input[i])`, requiring the target threshold and forbidding the next one.
- `--cardinality network`: builds an odd-even sorting network of two-way OR/AND comparators (padded with false) so the sorted outputs encode the exact count.

Constants and duplicate subcircuits are simplified away, and every remaining gate is a two-way equivalence forced by the cell variables. Ordinary model counts and projected counts are both preserved.

## A smaller equivalent system using boundary differences

`--marginal-system boundary` enforces the three top-role color counts first, then equates top with left, left with middle, and middle with right. Shared cells cancel out, leaving boundary sets of sizes 17 vs. 17, 9 vs. 9, and 9 vs. 9 for ternary boards.

For equal-sized sets `A` and `B`, matching color counts is equivalent to

`sum(color indicators on A) + sum(negated color indicators on B) = |B|`.

That shrinks the extra counters from length 81 down to lengths 34, 18, and 18 per color, with the exact same logical strength. `--marginal-system both` emits both versions, and `--omit-last-color` drops the redundant last color count.

With full ternary orbit breaking, formula sizes compare as follows (though smaller formulas do not guarantee faster counting):
- Baseline: 13,543 variables, 62,090 clauses
- Direct role counters: 36,211 variables / 151,502 clauses (sequential), or 33,781 variables / 122,828 clauses (network)
- Boundary system: 21,388 variables / 92,867 clauses (sequential), or 21,319 variables / 85,442 clauses (network)

## Verification and benchmark results

```sh
python experiments/exact_marginal_check.py
```

All **102 exact-count checks passed** (`exact_marginal_check.log`), testing both circuits against exact binomial counts on 0 to 7 inputs, negated literal inputs, and full binary boards across all combinations of the three marginal systems and optional LM/MR/TM pair marginals (**168** unrestricted, **42** orbit-normalized, counted over all variables without projection).

On the known seven-row ternary prefix C, both boundary encodings returned **2**: 33.753 CPU seconds (sequential) and 27.163 CPU seconds (network), both slower than the 16.28 CPU seconds of the plain model without marginal circuits. The larger direct-role encodings timed out at 90 wall seconds (`exact_marginal_prefix_results.json` and `exact_marginal_boundary_prefix_results.json`; CPU times are logged separately from wall limits under concurrent load).

Unrestricted baseline, direct-role sequential, and direct-role network formulas all timed out at 120 wall seconds (~41, 47, and 46 CPU seconds) without a count, stopping right after Ganak's formula summary with no counting log lines (`exact_marginal_full_results.json`).

Reading Ganak's source explained why: right after printing the summary, Ganak runs a standalone CryptoMiniSat (CMS) satisfiability solve before entering the counting loop ([`counter.cpp`, line 1161](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L1161)), and `--polar` does not affect that initial SAT check. So missing progress lines reflected a stalled SAT startup, not counting throughput. That affected these unphased **orbit-normalized** runs and the earlier 60-second orbit run, whereas the older 120-second palette-only run (`exact_count_ternary_support.log`) had entered counting and logged 148,916 conflicts and 0 cache hits.

Because bundled CMS tests constant assignments first, starting with all-false ([CMS `Lucky::doit`](https://github.com/msoos/cryptominisat/blob/97c6efeae45d93c45d2ebc3e4e83c2014c79513d/src/lucky.cpp#L228)), we built `exact_phase.py` to flip variables around a known full satisfying assignment so all-false becomes a valid model while preserving the model set bijectively.

Passing `--phase-seed 0` derives every auxiliary from a known board by unit propagation, checks every clause, and complements variables accordingly. The rephased binary boundary model still counted **42** over all variables.

Both rephased unrestricted marginal models cleared the initial SAT check immediately and entered counting (initializing components and running at least one learned-clause database reduction), then still timed out at 120 wall seconds without a count or conflict total: 24.182 CPU seconds for the boundary model and 27.198 CPU seconds for the direct-role model (`exact_marginal_phase_results.json`). This confirms counting started, without showing a speedup or completion estimate.

## Reproduction

```sh
python experiments/exact_marginal_cnf.py --orbit-canonical --independent-support --marginal-system boundary --cardinality network --phase-seed 0 experiments/exact_marginal_phase_boundary.cnf
python experiments/exact_marginal_benchmark.py --seconds 120 --jobs 1 --output experiments/exact_marginal_replay.json experiments/exact_marginal_phase_boundary.cnf
```

The benchmark wrapper runs deterministic Ganak (`--prob 0`, no approximate fallback) and logs exact commands, exit codes, wall and CPU times, peak RSS, and any solver stats, recording `exact_count: null` on timeout. These are external solver benchmarks rather than Lean proofs.
