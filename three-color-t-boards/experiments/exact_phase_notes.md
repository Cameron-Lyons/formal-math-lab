# Reaching exact counting with a known satisfying assignment

The unrestricted ternary count is still **not evaluated**. This experiment
removes a startup bottleneck in Ganak without removing any boards from the
counted set.

## Which earlier computation was blocked

Ganak 2.9.0 runs a SAT solver before entering its model-counting search. The
earlier **orbit-normalized** ternary run stalled inside that initial SAT call,
as did the new unphased orbit-normalized marginal runs. By contrast, the
earlier **palette-only** run did reach counting; its 148,916 conflicts and zero
cache hits came from counting search. Those two cases should not be mixed up.
The initial SAT check and counting setup appear in the
[pinned Ganak source](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L1161).

Before normal SAT search, the bundled CryptoMiniSat tries a few simple constant
assignments. Its
[pinned `Lucky::doit` implementation](https://github.com/msoos/cryptominisat/blob/97c6efeae45d93c45d2ebc3e4e83c2014c79513d/src/lucky.cpp#L228)
tests the all-false assignment first. We can transform the formula so a known
valid board becomes that all-false assignment.

## Why the complete count is unchanged

Let `F(x)` be the existing board CNF and let `a` be a verified satisfying
assignment. Define

```text
G(y) = F(y XOR a).
```

Because `y -> y XOR a` is its own inverse, it gives a bijection between all
models of `G` and all models of `F`, with `G(0) = F(a) = true`. On clauses,
this just flips the polarity of every variable set to true in `a`. It adds no
clauses, introduces no variables, and fixes no board cells. The symmetry
multiplier for the orbit-normalized ternary model remains 12.

[exact_phase.py](exact_phase.py) builds `a` by plugging a known board into the
one-hot cell variables and unit-propagating the functional auxiliary gates. It
rejects any contradiction or undetermined auxiliary, evaluates every original
clause independently, and checks that every transformed clause contains at
least one negative literal, directly confirming the all-false assignment.

Optional independent-support hints keep the same variable indices. Flipping
variable signs is also bijective on the support, so count preservation is
unaffected.

## Verification and runs

[The check program](exact_phase_check.py) passed 6,300 exhaustive truth-table
comparisons on small formulas, verified rejection of contradictory models, and
checked every variable across 36 board models. Rephased binary formulas still
count 168 (unrestricted), 84 (palette-normalized), and 42
(full-orbit-normalized) across all four occurrence encodings, counting all
Boolean variables with no projection hint. See [Check log](exact_phase_check.log).

The unrestricted orbit-normalized rephased formula keeps the original 13,543
variables and 62,090 clauses. Its log clears the initial SAT call and prints
component setup (`[bce]`) followed by learned-clause reductions (`[rdb]`)
during counting search. The phased marginal formulas also clear that startup
gate. Getting past startup is real progress, though it does not mean the count
will finish in time. See [Baseline counting log](exact_phase_ternary.log) and
[marginal experiments](exact_marginal_notes.md).

The baseline run hit its **600-second wall limit** and exited with timeout
status 124. Its last recorded CPU time was 139 seconds at 596 seconds elapsed,
because other jobs ran on the machine concurrently. It reached the 22nd
learned-clause database reduction without emitting a count, and the process has
exited. See [Command, input hash, and terminal status](exact_phase_run.json).

Two alternative counting-polarity settings also entered counting and timed out
after 120 wall seconds each, while still reproducing the binary count 42. They
do not show a speed advantage for either policy. See
[Polarity results and source analysis](exact_phase_polar_notes.md).

Run from the project root:

```sh
python experiments/exact_phase_check.py
python experiments/exact_phase.py experiments/exact_phase_ternary.cnf
timeout 600s experiments/exact_count_tools/ganak --prob 0 --arjun 0 --puura 0 --td 0 --maxcache 512 experiments/exact_phase_ternary.cnf
```

The first ternary witness comes from the original certificate; see the
[attribution and license notices](../sources/README.txt). Neither this
rephasing nor external solver outputs are Lean proofs of an unrestricted total.
A finished exact count is still needed, and a timeout gives no total.
