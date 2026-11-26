# Exact reduction to 16 quadruple counts and 65 triple counts

This gives an equivalent formulation of the unrestricted counting problem; it
does not compute the unrestricted count.

Let `C(t,l,m,r)` be the number of T placements matching an ordered color
quadruple. Require `C(p) = 1` for the **16** patterns with all coordinates in
`{0, 1}`, and require each of the following **65** triple sums to equal **3**:

- Omit top: all 27 choices of `(left, middle, right)`.
- Omit left: top in `{0, 1}`, middle and right arbitrary (18 lines).
- Omit middle: top and left in `{0, 1}`, right arbitrary (12 lines).
- Omit right: top, left, and middle in `{0, 1}` (8 lines).

Together, these 65 line sums and 16 base counts force all 81 quadruple counts
to equal 1.

## Proof

Induct on the number of 2s in a pattern `p`. With zero 2s, `p` is one of the 16
base constraints. Otherwise, let `j` be the first coordinate equal to 2. Every
earlier coordinate is 0 or 1, so the list above includes the line that drops
coordinate `j`. Its other two patterns replace that 2 with 0 and 1; both have
one fewer 2, so by induction both already have count 1. The line sum then gives
`1 + 1 + C(p) = 3`, so `C(p) = 1`.

In matrix terms, each chosen line has a unique pivot pattern whose first 2 lies
at the omitted slot. Sorting patterns by how many 2s they contain makes the
81-equation system unit triangular. This proof relies only on counting
identities, not on any property of known boards.

One line is redundant: the omitted-top line for lower triple `222`. Since the
27 omitted-top lines partition all 81 placements, fixing the other 26 sums to 3
forces the last one to be `81 - 26*3 = 3`. So **80 explicit cardinality
constraints** already suffice. Pass `--drop-one-line` to omit it (by default
all 81 are kept).

For `q` colors, replace 2 with `q-1`: there are `(q-1)^4` base patterns and
`q^3+(q-1)q^2+(q-1)^2q+(q-1)^3` selected lines, each summing to `q`. For binary
boards (`q=2`), that is 1 base count and 15 line sums of 2.

## Parsimonious CNF implementation

`exact_reduced_cnf.py` uses one-hot cell variables, conjunction gates for the
selected occurrences, and functional exact-cardinality circuits from
`exact_marginal_cnf.py`. Exact-one counts use a functional OR tree, while
larger targets use sequential threshold circuits or sorting networks. Because
every auxiliary variable is uniquely determined by the cell colors, ordinary
model counting matches board counting directly, and optional projection onto
cell variables gives the same count.

Color and reflection normalization reuse the verified normalization clauses; an
orbit-normalized ternary model count must be multiplied by 12. Rephasing via
`exact_phase.py` flips variable polarities using a verified complete board so
the solver hits its initial SAT witness immediately, without changing the count
or fixing any cells. Witnesses keep the provenance from the original source
certificates.

The default orbit-normalized ternary CNF has **30,487 variables and 109,794
clauses** (16 quadruple and 65 triple constraints). The fixed seven-row prefix
C CNF has 10,152 variables and 35,324 clauses. Smaller or different clause
counts do not by themselves imply faster solving.

## Checks

```sh
python experiments/exact_reduced_check.py
```

All **16 exact-count checks passed** across both cardinality circuit types and
both `--drop-one-line` settings. The unrestricted binary count stays **168**
and its orbit count stays **42**. The finite layout test verifies the
triangular pivot order for palette sizes 1, 2, and 3.

The suite also checks the explicit uniform-triple counterexample in
`exact_structure_counterexample.json`. It passes all 65 triple sums yet has
only 73 distinct quadruples (with `1111` appearing twice), so the 16 base
constraints reject it. That guards against wrongly assuming triple marginals
alone imply validity. Fully fixed valid ternary certificates still count as 1
model.

## Reproduction

```sh
python experiments/exact_reduced_cnf.py --orbit-canonical --independent-support --phase-seed 0 experiments/exact_reduced_ternary.cnf
python experiments/exact_reduced_cnf.py --prefix-json sources/anc/certificates.json --prefix-name C --independent-support --phase-seed 1 experiments/exact_reduced_prefix_C.cnf
python experiments/exact_reduced_benchmark.py --seconds 120 --jobs 2 --output experiments/exact_reduced_bench_results.json experiments/exact_reduced_ternary.cnf experiments/exact_reduced_prefix_C.cnf
```

The benchmark runs deterministic Ganak with no approximate fallback, records
incomplete runs as `exact_count: null`, and logs CPU time separately from wall
limits. Before writing a phased CNF, the script verifies the all-false witness
by unit propagation and direct clause evaluation. External model-counter runs
are not Lean proofs.

Both the unrestricted and prefix-C runs cleared initial SAT and entered
counting, then timed out at 120 wall seconds (55.930 and 60.039 CPU seconds).
The unrestricted run reached its third clause-database reduction and prefix C
reached its ninth, with neither returning a count. In particular, this bounded
run did not reproduce prefix C's known count of 2. These runs check an
alternative exact encoding rather than showing a speedup. Both processes have
exited; full logs are in `exact_reduced_bench_results.json`.
