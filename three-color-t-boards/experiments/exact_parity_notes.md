# Exact parity formulation

Requiring every T-pattern occurrence count to be **odd** is exactly equivalent
to validity. There are `q^4` nonnegative counts and their sum is `q^4`; if each
is odd, each is at least one, so each must equal one. The converse is immediate.
The parent development formalizes this as
`TBoards.ExactParity.valid_iff_odd` in `ExactParity.lean`.

This yields a new exact CNF formulation and an algebraic representation, but
the bounded experiments below did **not** produce the unrestricted ternary
count or demonstrate a counting speed improvement.

## Parsimonious encoding

`exact_parity_cnf.py` retains one-hot cell indicators and defines a selector
for each compatible `(placement, pattern)` pair as the conjunction of its
cell colors. For each pattern it requires the XOR of its occurrence selectors
to be true. Fixed-prefix occurrences contribute Boolean constants to this
equation. Unlike the earlier exact-one encoding, this model does not exclude
patterns already used in the prefix; their full occurrence parity is checked.

The default circuit is a chain of gates `z <-> a XOR b`. All four forbidden
input/output assignments are excluded by CNF clauses, making each auxiliary
uniquely determined. A balanced-tree layout is also implemented and checked.
Ordinary, unprojected model counting therefore counts boards without an
auxiliary multiplicity factor. Per-pattern OR and at-most-one constraints are
not included. The existing functional symmetry comparator can select one
representative per full color/reflection orbit; a completed ternary count in
this mode would be multiplied by 12.

The `--connected` variant additionally requires:

- XOR of all pattern selectors at each placement equals one: 81 equations.
- For each role and each of the first `q-1` colors, XOR of its cell indicators
  equals `q^3 mod 2`: eight equations for ternary boards, four for binary boards.

These constraints follow from validity and use functional XOR gates as well.
Their shared selectors connect the otherwise separate per-pattern equations.

| Full orbit-normalized CNF | Variables | Clauses |
| --- | ---: | ---: |
| Pattern parity chains | 13,543 | 62,009 |
| Chains with window and unary parities | 20,663 | 90,578 |

The conceptual native XOR systems have coefficient ranks **81 of 81** and
**169 of 170** over `F_2`, respectively. The connected system's one dependency
comes from summing all pattern equations versus summing all window equations.
These ranks were computed directly on the emitted equation coefficients and
recorded in `exact_parity_linear_structure.json`. They do not solve the board
problem: occurrence selectors are still nonlinear functions of the cells.

## Native XOR and Gaussian support

The installed Ganak CLI does **not** accept native XOR constraints. A tiny
input consisting of three variables and `x1 2 3 0` should have four models;
Ganak instead exits with status 1 before counting. This is explained exactly
by its pinned Arjun dependency:
[`SimplifiedCNF::add_xor_clause`](https://github.com/meelgroup/arjun/blob/c86963a05108092cba6fa10e35403053bd175e4d/src/arjun.h#L1673)
has two overloads, both implemented as unconditional `exit(EXIT_FAILURE)`.
Ganak parses into that class even with `--arjun 0`. The probe input, output,
command, terminal status and source explanation are retained under
`exact_parity_native_probe.*`.

CryptoMiniSat itself supports native XORs, automatic XOR extraction, and
Gaussian elimination. At the pinned revision, its defaults enable XOR
discovery and include `occ-xor` in simplification schedules; see
[`solverconf.cpp`](https://github.com/msoos/cryptominisat/blob/97c6efeae45d93c45d2ebc3e4e83c2014c79513d/src/solverconf.cpp#L220).
Its Gaussian configuration permits matrices with at least ten rows and
can disable unhelpful elimination dynamically; see
[`solverconf.h`](https://github.com/msoos/cryptominisat/blob/97c6efeae45d93c45d2ebc3e4e83c2014c79513d/src/solverconf.h#L54).

Those capabilities do not imply Gaussian propagation in Ganak's counting
search. Ganak builds a separate CMS solver for initial satisfiability and
selected oracle checks, while its main counting propagation and internal SAT
mode use Ganak's own clause machinery. The exposed `--xorgatemaxsize` option
belongs to Puura's gate detection and is not a switch for native Gaussian
counting. Relevant pinned sources are
[`counter.cpp`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L1153)
and [`main.cpp`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/main.cpp#L244).
No Gaussian counting benefit is claimed for these trials.

The encoder can export standard CryptoMiniSat-style XOR lines with
`--layout native`, including correct sign changes under witness rephasing.
That exporter is for a future compatible backend; it was not used to claim
an exact count. The source files inspected, their revisions, URLs and hashes
are recorded in `exact_parity_source_provenance.json`.

## Validation

`exact_parity_check.py --prefix --seconds 90` completed:

- **1,016 input-assignment checks** of functional chains and trees, including
  negative literals, canceled duplicate variables, constants, empty equations,
  both parity targets, and complete propagation of every auxiliary.
- **10 exact ordinary model-count checks**: binary 168 and orbit-normalized
  42 for plain chains, balanced trees and connected chains; fixed valid ternary
  count 1 and fixed invalid ternary count 0 for both chain variants.
- **10 complete ternary model checks**: five published seed boards, each with
  both unrestricted orbit-normalized chain variants. Fixing the cell colors
  determines every auxiliary by unit propagation and satisfies every clause.

The invalid ternary board is the existing uniform-three-coordinate-marginal
counterexample with 73 distinct patterns. Its eight missing and eight doubled
patterns violate 16 of the parity equations, so the fixed board is rejected.

Both prefix C parity variants timed out after 90 wall seconds without a count.
The known exact count remains 2 from the other methods; it was **not**
reproduced by these parity-prefix trials. Their sizes are 5,958 variables /
26,097 clauses and 9,158 / 38,950. Terminal records and the validation summary
are in `exact_parity_check_results.json` and `exact_parity_check_summary.json`.

## Full trials

Exactly two full trials were run, using the distinct plain and connected
circuits. Both were rephased using a verified known complete board so all-false
is a witness, without fixing any cell or changing the count. The deterministic
Ganak options were:

```text
--prob 0 --arjun 0 --puura 0 --td 0 --maxcache 512 --polar 3 --verb 2
```

Approximate fallback was not enabled. Each subprocess had a 90-second wall
limit. CPU time below is OS user plus system CPU time, not wall time.

| Circuit | Terminal status | CPU seconds | Wall seconds | Peak RSS, KB |
| --- | --- | ---: | ---: | ---: |
| Plain chains | timeout; no count | 68.039 | 90.035 | 93,136 |
| Connected chains | timeout; no count | 68.237 | 90.025 | 123,944 |

Both passed initial satisfiability and reached their sixth recorded clause
database reduction. Thus actual counting search occurred. Neither reported a
completed count or a final conflict total, and a missing result is never
interpreted as zero. The tests ran concurrently, so these timings do not
establish a fine-grained performance comparison. No third full trial was run,
and every parity process has ended.

`exact_parity_runs.json` records exact commands, input hashes, limits, statuses,
resource usage and observed counting progress. Full CNFs, metadata and logs
are `exact_parity_chain.*` and `exact_parity_connected.*`.

## Reproduction

```sh
python experiments/exact_parity_check.py --prefix --seconds 90
python experiments/exact_parity_cnf.py --orbit-canonical --phase-seed 0 --independent-support experiments/exact_parity_chain.cnf
python experiments/exact_parity_cnf.py --orbit-canonical --phase-seed 0 --independent-support --connected experiments/exact_parity_connected.cnf
python experiments/exact_parity_benchmark.py --seconds 90
```

The benchmark refuses to launch unless ordinary binary counts 168 and 42 have
passed for each of the two tested variants. The Lean equivalence and the
parsimonious circuits establish an exact reformulation; the unrestricted
ternary numerical count remains unresolved.
