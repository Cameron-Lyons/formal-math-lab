# Exact parity formulation

Requiring every T-pattern count to be **odd** is equivalent to board validity.
There are `q^4` nonnegative counts summing to `q^4`; if every count is odd,
every count is at least 1, so every count must be 1. The converse is immediate.
This equivalence is formalized as `TBoards.ExactParity.valid_iff_odd` in
`ExactParity.lean`.

This gives a new exact CNF encoding and an algebraic formulation, though the
bounded runs below did **not** compute the unrestricted ternary count or show a
counting speedup.

## Parsimonious encoding

`exact_parity_cnf.py` uses one-hot cell indicators and defines a selector bit
for each compatible `(placement, pattern)` pair as the conjunction of its cell
colors. For each pattern, it requires the XOR of all occurrence selectors to be
true. Fixed-prefix occurrences enter as Boolean constants. Unlike the earlier
exact-one encoding, this model does not ban patterns already seen in the prefix;
it checks the parity of every pattern across the full board.

By default, each XOR equation is encoded as a chain of gates `z <-> a XOR b`.
All four forbidden input-output combinations are blocked by clauses, so every
auxiliary variable is uniquely determined by the cells. A balanced-tree layout
is also implemented and tested. Ordinary unprojected model counting therefore
counts boards directly with no auxiliary multiplicity. Per-pattern OR and
at-most-one clauses are omitted. The existing functional symmetry comparator can
pick one canonical representative per color/reflection orbit; a finished
ternary count in that mode would be multiplied by 12.

The `--connected` variant adds two sets of redundant functional XOR equations:

- The XOR of all pattern selectors at each placement equals 1 (81 equations).
- For each role and each of the first `q-1` colors, the XOR of its cell
  indicators equals `q^3 mod 2` (8 equations for ternary boards, 4 for binary).

Both sets follow from validity and use shared selectors that couple the
otherwise separate per-pattern equations.

| Full orbit-normalized CNF | Variables | Clauses |
| --- | ---: | ---: |
| Pattern parity chains | 13,543 | 62,009 |
| Chains with window and unary parities | 20,663 | 90,578 |

The underlying native XOR systems have coefficient ranks **81 of 81** and
**169 of 170** over `F_2`. The single dependency in the connected system comes
from comparing the sum of all pattern equations against the sum of all window
equations. These ranks come directly from the emitted equation coefficients and
are saved in `exact_parity_linear_structure.json`. They do not solve the board
problem on their own because the occurrence selectors are nonlinear in the cell
variables.

## Native XOR and Gaussian support

The installed Ganak CLI does **not** support native XOR clauses. On a tiny test
input with three variables and `x1 2 3 0` (which has 4 models), Ganak exits
with status 1 before counting. Its pinned Arjun dependency explains why: both
overloads of
[`SimplifiedCNF::add_xor_clause`](https://github.com/meelgroup/arjun/blob/c86963a05108092cba6fa10e35403053bd175e4d/src/arjun.h#L1673)
call `exit(EXIT_FAILURE)` unconditionally, and Ganak parses into that class
even with `--arjun 0`. The test input, output, command, exit status, and source
notes are saved under `exact_parity_native_probe.*`.

CryptoMiniSat itself supports native XOR clauses, automatic XOR extraction, and
Gaussian elimination. At the pinned revision, its defaults enable XOR discovery
and include `occ-xor` in simplification schedules (see
[`solverconf.cpp`](https://github.com/msoos/cryptominisat/blob/97c6efeae45d93c45d2ebc3e4e83c2014c79513d/src/solverconf.cpp#L220)).
Its Gaussian settings allow matrices with at least 10 rows and can turn off
unhelpful elimination dynamically (see
[`solverconf.h`](https://github.com/msoos/cryptominisat/blob/97c6efeae45d93c45d2ebc3e4e83c2014c79513d/src/solverconf.h#L54)).

That does not mean Ganak uses Gaussian propagation during counting search.
Ganak calls a separate CryptoMiniSat instance for initial SAT and selected
oracle queries, while its main counting propagation and internal SAT mode use
Ganak's own clause engine. The `--xorgatemaxsize` flag belongs to Puura's gate
detection and does not turn on native Gaussian counting. See the pinned sources
[`counter.cpp`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L1153)
and [`main.cpp`](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/main.cpp#L244).
We claim no Gaussian counting speedup from these runs.

The encoder can still export CryptoMiniSat-style XOR lines with
`--layout native`, including the right sign flips under witness rephasing, for
use with a compatible backend later. That mode was not used to claim any count.
Inspected source files, revisions, URLs, and hashes are listed in
`exact_parity_source_provenance.json`.

## Validation

`exact_parity_check.py --prefix --seconds 90` passed:

- 1,016 input-assignment checks on functional chains and trees, covering
  negative literals, canceled duplicate variables, constants, empty equations,
  both parity targets, and full propagation of every auxiliary bit.
- 10 exact ordinary model-count checks: binary counts 168 and orbit-normalized
  42 for plain chains, balanced trees, and connected chains, plus fixed valid
  ternary count 1 and fixed invalid ternary count 0 for both chain variants.
- 10 full ternary model checks across the five published seed boards on both
  unrestricted orbit-normalized chain variants: fixing the cell colors forces
  every auxiliary by unit propagation and satisfies every clause.

The invalid ternary test board is the uniform-three-coordinate-marginal
counterexample with 73 distinct patterns. Its 8 missing and 8 doubled patterns
violate 16 parity equations, so it is rejected.

Both prefix-C parity runs timed out after 90 wall seconds with no count, so they
did **not** reproduce the known exact count of 2 from other methods. Their CNF
sizes are 5,958 variables / 26,097 clauses and 9,158 variables / 38,950
clauses. Terminal records and validation outputs are in
`exact_parity_check_results.json` and `exact_parity_check_summary.json`.

## Full trials

We ran two full trials, one for plain chains and one for connected chains. Both
were rephased using a verified board so all-false is a satisfying assignment,
without fixing any cell or changing the count. Both used deterministic Ganak
options:

```text
--prob 0 --arjun 0 --puura 0 --td 0 --maxcache 512 --polar 3 --verb 2
```

Approximate fallback stayed off, and each subprocess had a 90-second wall
limit. CPU time below is OS user plus system CPU time, separate from wall time.

| Circuit | Terminal status | CPU seconds | Wall seconds | Peak RSS, KB |
| --- | --- | ---: | ---: | ---: |
| Plain chains | timeout; no count | 68.039 | 90.035 | 93,136 |
| Connected chains | timeout; no count | 68.237 | 90.025 | 123,944 |

Both runs passed initial SAT and reached their sixth clause-database reduction,
confirming that counting search was running. Neither printed a count or a final
conflict total, and a missing count is never read as zero. Because the two runs
executed at the same time, their timings do not give a tight speed comparison.
No third full trial was run, and both processes have exited.

`exact_parity_runs.json` logs exact commands, input hashes, limits, exit
statuses, resource usage, and counting progress. The CNFs, metadata, and logs
are saved as `exact_parity_chain.*` and `exact_parity_connected.*`.

## Reproduction

```sh
python experiments/exact_parity_check.py --prefix --seconds 90
python experiments/exact_parity_cnf.py --orbit-canonical --phase-seed 0 --independent-support experiments/exact_parity_chain.cnf
python experiments/exact_parity_cnf.py --orbit-canonical --phase-seed 0 --independent-support --connected experiments/exact_parity_connected.cnf
python experiments/exact_parity_benchmark.py --seconds 90
```

The benchmark refuses to start unless ordinary binary counts 168 and 42 pass
for both tested variants. The Lean proof and parsimonious circuits give a valid
exact reformulation, while the unrestricted ternary count remains open.
