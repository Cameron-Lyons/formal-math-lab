# Exact reduction to 16 quadruple counts and 65 triple counts

This is an equivalent formulation of the unrestricted counting problem, not
an evaluated unrestricted count.

Let `C(t,l,m,r)` be the number of T placements carrying an ordered color
quadruple. Require `C(p)=1` for the **16** patterns whose coordinates all lie
in `{0,1}`. In addition, require each of the following selected triple counts
to equal **3**:

- Omit top: all 27 choices of `(left,middle,right)`.
- Omit left: top is 0 or 1; middle and right are arbitrary. There are 18 lines.
- Omit middle: top and left are 0 or 1; right is arbitrary. There are 12 lines.
- Omit right: top, left, and middle are all 0 or 1. There are 8 lines.

These **65** line sums, together with the 16 base counts, force every one of
the 81 quadruple counts to equal 1.

## Proof

Induct on the number of coordinates of a pattern `p` equal to 2. The case
with no 2 is one of the 16 base constraints. Otherwise let `j` be the first
coordinate equal to 2. All earlier coordinates are 0 or 1, so the line that
omits coordinate `j` is included above. Its other two patterns replace that
2 by 0 and 1; each has one fewer 2 and therefore already has count 1.
The line sum gives `1 + 1 + C(p) = 3`, hence `C(p)=1`.

Equivalently, each selected line has a unique pivot pattern whose first 2
is its omitted coordinate. Ordering patterns by their number of 2s makes
the full 81-equation count system unit triangular. This also shows that the
reduction does not rely on a special property of discovered boards.

One selected line can be omitted: the omitted-top line with lower triple
`222`. The 27 omitted-top lines partition all 81 placements, so its count is
81 minus the other 26 counts of 3, which is 3. Thus the board's known number
of placements makes **80 explicit cardinality constraints** sufficient.
The program offers this as `--drop-one-line`; the default retains all 81.

For `q` colors, replace 2 by `q-1`. There are `(q-1)^4` base patterns and
`q^3+(q-1)q^2+(q-1)^2q+(q-1)^3` selected lines, each with target `q`.
For binary boards this gives one base count and 15 line sums of 2.

## Parsimonious CNF implementation

`exact_reduced_cnf.py` creates one-hot cell variables, conjunction gates for
the selected occurrences, and functional exact-cardinality circuits from
`exact_marginal_cnf.py`. Exact-one occurrences use a functional OR tree;
larger targets use sequential threshold circuits or sorting networks. Every
auxiliary value is uniquely determined by the board. Consequently ordinary
model counts equal board counts; optional projection onto cell variables
preserves the same count.

Color and reflection normalization reuse the existing verified normalization
encoding. A ternary orbit-normalized model count must be multiplied by 12.
Rephasing through `exact_phase.py` complements individual Boolean variables
according to a verified complete witness. This changes no count and fixes no
board cells; it lets the solver immediately find its initial SAT witness.
The witnesses retain the provenance in the existing source certificates.

The default orbit-normalized ternary model has **30,487 variables and
109,794 clauses**, with 16 quadruple constraints and 65 triple constraints.
The fixed seven-row prefix C model has 10,152 variables and 35,324 clauses.
These sizes do not establish a performance advantage.

## Checks

```sh
python experiments/exact_reduced_check.py
```

All **16 exact-count checks passed**, using both cardinality methods and
both choices of whether to drop the redundant line. The unrestricted binary
count remains **168** and its full symmetry-orbit count remains **42**.
The finite layout check confirms the triangular pivot structure for palettes
of sizes 1, 2, and 3.

The test also checks the explicit uniform-triple counterexample in
`exact_structure_counterexample.json`. It satisfies all 65 selected triple
conditions but has 73 distinct quadruples, including `1111` twice. The base
quadruple constraints correctly reject it. This prevents the invalid shortcut
of assuming triple marginals alone imply validity. Completely fixed valid
ternary certificates still count as exactly one model.

## Reproduction

```sh
python experiments/exact_reduced_cnf.py --orbit-canonical --independent-support --phase-seed 0 experiments/exact_reduced_ternary.cnf
python experiments/exact_reduced_cnf.py --prefix-json sources/anc/certificates.json --prefix-name C --independent-support --phase-seed 1 experiments/exact_reduced_prefix_C.cnf
python experiments/exact_reduced_benchmark.py --seconds 120 --jobs 2 --output experiments/exact_reduced_bench_results.json experiments/exact_reduced_ternary.cnf experiments/exact_reduced_prefix_C.cnf
```

The benchmark uses deterministic Ganak with no approximate fallback and
records incomplete runs as `exact_count: null`. It reports CPU usage
separately from wall limits. Every complete all-false witness is checked by
unit propagation and evaluation of all clauses before a phased model is
written. The external model-counting computations are not Lean certificates.

The recorded unrestricted and prefix-C trials both passed initial SAT and
entered actual counting, but both timed out after 120 wall seconds. They used
55.930 and 60.039 CPU seconds respectively. The unrestricted run reached its
third recorded learned-clause database reduction; the prefix run reached its
ninth. Neither returned a completed count. In particular, this bounded run
did not reproduce prefix C's independently known count of 2. The results
establish a correct alternative formulation, not a measured speedup. Both
benchmark processes ended; details are in `exact_reduced_bench_results.json`.
