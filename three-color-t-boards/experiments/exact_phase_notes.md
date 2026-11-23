# Reaching exact counting with a known satisfying assignment

The unrestricted ternary total is still **not evaluated**. This experiment
removes an observed startup bottleneck without removing any boards from the
counted set.

## Which earlier computation was blocked

Ganak 2.9.0 calls a SAT solver before entering its model-counting search.
The earlier **orbit-normalized** ternary run stopped at that initial SAT
call, as did the new unphased orbit-normalized marginal trials. The earlier
**palette-only** run did reach counting; its recorded 148,916 conflicts and
zero cache hits were counting statistics. These cases must not be conflated.
The initial call and the subsequent counting initialization are visible in
the [pinned Ganak source](https://github.com/meelgroup/ganak/blob/f262be5374f312b4bf7c99c6cca26e51182158e5/src/counter.cpp#L1161).

The bundled SAT solver tries simple constant assignments before ordinary
search. Its [pinned `Lucky::doit` implementation](https://github.com/msoos/cryptominisat/blob/97c6efeae45d93c45d2ebc3e4e83c2014c79513d/src/lucky.cpp#L228)
tries the all-false assignment first. We can make an already known board
have exactly that Boolean representation.

## Why the complete count is unchanged

Let `F(x)` be the existing board CNF and let `a` be a fully verified model.
Define

```text
G(y) = F(y XOR a).
```

The map `y -> y XOR a` is its own inverse. Therefore it bijects **all** models
of `G` with **all** models of `F`. Also `G(0)=F(a)=true`. At the clause level,
this only complements every occurrence of a variable whose value in `a` is
true. No clauses are added, no variables are introduced, and no board cells
are fixed by the transformation. The original symmetry multiplier remains
twelve for the orbit-normalized ternary model.

[exact_phase.py](exact_phase.py) obtains `a` by supplying a known board to
the original one-hot cell variables and unit-propagating the functional
auxiliary definitions. It rejects contradictions and any undetermined
auxiliaries, evaluates every original clause independently, then checks
that every transformed clause has a negative literal. That last check
directly verifies the all-false assignment.

Optional independent-support hints retain the same variable indices.
Complementing variables is bijective on the support as well, so their
count-preserving property is unchanged.

## Verification and runs

[The check program](exact_phase_check.py) passed 6,300 exhaustive Boolean
truth-table comparisons on small formulas, verifies rejection of
contradictory models, and checks all variables in 36 board models. The
rephased binary formulas still count 168, 84, and 42 for unrestricted,
palette-normalized, and full-orbit-normalized boards, respectively, across
all four occurrence encodings. The binary checks count all Boolean
variables without a projection hint. [Check log](exact_phase_check.log)

The unrestricted orbit-normalized rephased formula has the original
13,543 variables and 62,090 clauses. Its log passes the initial SAT call
and records component initialization (`[bce]`) followed by learned-clause
reductions (`[rdb]`) in the counting search. The phased marginal formulas
also pass that startup gate. Reaching counting is progress in the
computation, not evidence that it has finished. [Baseline counting log](exact_phase_ternary.log)
and [marginal experiments](exact_marginal_notes.md).

The baseline run then reached its **600-second wall limit** and exited with
timeout status 124. The last observed CPU usage was 139 seconds at 596
seconds elapsed, reflecting concurrent work on this machine. It had reached
the 22nd reported learned-clause database reduction, but emitted no completed
exact count. The process was verified terminated.
[Command, input hash, and terminal status](exact_phase_run.json)

Two alternative counting-polarity settings also entered counting and timed
out after 120 wall seconds each. Both still reproduce the binary count 42.
These trials do not establish a runtime advantage for either policy.
[Polarity results and source analysis](exact_phase_polar_notes.md)

From the project root:

```sh
python experiments/exact_phase_check.py
python experiments/exact_phase.py experiments/exact_phase_ternary.cnf
timeout 600s experiments/exact_count_tools/ganak --prob 0 --arjun 0 --puura 0 --td 0 --maxcache 512 experiments/exact_phase_ternary.cnf
```

The first ternary witness is adapted from the original certificate, with
the original [attribution and license notices](../sources/README.txt).
The transformation and ordinary external solver counts are not Lean
certificates of an unrestricted total. A completed exact model count is
still required; a timeout supplies no such total.
