# Functional marginal constraints for exact counting

No unrestricted ternary count has been obtained by these experiments.
`exact_marginal_cnf.py` extends the parsimonious model in `exact_count_cnf.py`
without changing that file. It adds necessary exact-cardinality constraints,
using uniquely determined auxiliary variables.

For each of the four T roles (top, left, middle, right), every color occurs
exactly 27 times among the 81 patterns. Each role occupies 81 distinct board
cells. Therefore the indicator variables for one color in one role sum to
27. The analogous targets are 8 on 16 cells for binary boards. Optional
pair marginals require every ordered color pair to occur exactly 9 times
in any two roles (4 times for binary boards).

Two count-preserving circuit encodings are implemented:

- `--cardinality sequential`: each threshold variable is defined by
  `s[i,k] iff s[i-1,k] OR (s[i-1,k-1] AND input[i])`. Requiring the target
  threshold and prohibiting the next threshold gives an exact count.
- `--cardinality network`: an odd-even sorting network uses Boolean OR/AND
  comparators, each defined in both directions. Its sorted outputs encode
  the exact number of true inputs. Padding inputs are constant false.

Constants and identical subcircuits are simplified. Every remaining gate is
an equivalence, so its value is uniquely determined by the cell coloring.
These circuits preserve ordinary model counts, not only projected counts.

## A smaller equivalent system using boundary differences

`--marginal-system boundary` first enforces the three top-role counts, then
equates the top/left, left/middle, and middle/right color counts. Shared cells
cancel from each equation. For ternary boards the differences have sizes
17 versus 17, 9 versus 9, and 9 versus 9, respectively.

For equal-size sets A and B, equality of their color counts is equivalent to

`sum(color indicators on A) + sum(negated color indicators on B) = |B|`.

Thus the additional counters have only 34, 18, and 18 inputs per color,
instead of three more counters of length 81. This is logically equivalent
to enforcing all four role marginals. `--marginal-system both` adds both
versions, and `--omit-last-color` exploits the redundant last color count.

With ternary full-orbit normalization, the original model has 13,543
variables and 62,090 clauses. Adding all role counters gives 36,211 variables
and 151,502 clauses with sequential counters, or 33,781 variables and 122,828
clauses with sorting networks. The boundary system reduces this to 21,388
variables and 92,867 clauses, or 21,319 variables and 85,442 clauses,
respectively. A smaller formula is not a demonstrated runtime improvement.

## Verification and benchmark results

```sh
python experiments/exact_marginal_check.py
```

All **102 exact-count checks passed**. They check both circuit methods against
binomial counts for every target on 0 through 7 Boolean inputs, complementary
literal inputs, and the full binary board counts. For every combination of
the three marginal systems and optional LM/MR/TM pair marginals, binary
counts remain **168** unrestricted and **42** with full orbit normalization.
These tests count all auxiliaries directly, without a projection hint.
See `exact_marginal_check.log`.

The known seven-row ternary prefix C was counted exactly as **2** by both
boundary encodings: 33.753 CPU seconds for sequential counters and 27.163
CPU seconds for sorting networks. The earlier model without marginal
circuits took 16.28 CPU seconds on this prefix, so these tests do not establish
a speedup. The larger direct-role encodings did not finish within 90 wall
seconds. Timings came from concurrent experiments; CPU times are reported
separately from wall limits. See `exact_marginal_prefix_results.json` and
`exact_marginal_boundary_prefix_results.json`.

Unrestricted baseline, direct-role sequential, and direct-role network
formulas all timed out at 120 wall seconds. They used approximately 41, 47,
and 46 CPU seconds respectively. None returned a count. Their logs stopped
immediately after the solver's formula summary, without a counting-progress
report; see `exact_marginal_full_results.json`.

Source inspection identified a relevant obstacle: Ganak calls an independent
CMS satisfiability solve immediately after that summary and before its
counting loop. Thus absence of counting statistics must not be interpreted as
measured #SAT search throughput. The source location is
[`counter.cpp`, line 1161](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L1161).
The `--polar` option affects Ganak's counting decisions, not that initial
CMS solve.

This diagnosis concerns the unphased **orbit-normalized** runs in
`exact_marginal_full_results.json` and the earlier 60-second orbit-normalized
trial. It does **not** apply to every earlier unrestricted run: the older
palette-only 120-second trial (`exact_count_ternary_support.log`) did enter
counting and reported 148,916 conflicts and zero cache hits.

The bundled CMS version enables a preliminary check for constant assignments;
it tries all-false first. This motivates the separate `exact_phase*` work:
complement variables according to a known full satisfying assignment so
all-false becomes a witness, while preserving the model count bijectively.
See [CMS `Lucky::doit`](https://github.com/msoos/cryptominisat/blob/97c6efeae45d93c45d2ebc3e4e83c2014c79513d/src/lucky.cpp#L228).

This workaround was then tested. `--phase-seed 0` calls `exact_phase.py` to
derive every auxiliary value by unit propagation from a known board, verify
every clause, and complement variables so that this model becomes all-false.
The transformation changes neither the model count nor the set of represented
boards. The phased binary boundary model returned **42**, counting every
variable without projection.

Both phased unrestricted marginal models immediately passed the initial SAT
check and reached actual counting, evidenced by component initialization and
learned-clause database reductions. Both still timed out at 120 wall seconds:
the boundary model used 24.182 CPU seconds and the direct-role model 27.198.
Neither emitted a completed count or a periodic exact conflict total. Each
reached at least the first recorded learned-clause database reduction. These
runs establish that counting began; they do not establish a runtime advantage
or a likely completion time. See `exact_marginal_phase_results.json`.

## Reproduction

```sh
python experiments/exact_marginal_cnf.py --orbit-canonical --independent-support --marginal-system boundary --cardinality network --phase-seed 0 experiments/exact_marginal_phase_boundary.cnf
python experiments/exact_marginal_benchmark.py --seconds 120 --jobs 1 --output experiments/exact_marginal_replay.json experiments/exact_marginal_phase_boundary.cnf
```

The benchmark wrapper records the exact command, exit status, wall time,
CPU usage, maximum resident memory, and any reported conflict/decision
statistics. A timeout records `exact_count: null`. It uses deterministic
Ganak (`--prob 0`) with no approximate fallback. These external solver
experiments are not Lean certificates, and the marginal encodings make no
claim that the full count is practical.
