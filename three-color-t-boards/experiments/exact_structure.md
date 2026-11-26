# Exact-count structure: a failed relaxation and an exact replacement

This note does not evaluate the unrestricted ternary count. Its main finding is
an explicit counterexample showing that uniform three-coordinate marginals do
not imply full T-pattern uniqueness for ternary boards. Adding just sixteen
quadruple counts restores an exact characterization. The accompanying checks
also rule out two direct Euler-tour and determinant counting approaches.

Run the independent finite checks with:

```sh
python experiments/exact_structure_check.py
```

## Uniform three-coordinate marginals do not suffice for ternary boards

Consider this ternary board with the usual row lengths `1, 3, ..., 19`:

```text
1
000
01001
2102001
010000221
22102110022
0012011101121
220201221200220
21121111012122222
2021201011220210200
```

Let `C(t, l, m, r)` count its ordered T patterns. Every one of the 27 triples
appears exactly 3 times in **each** of the four three-coordinate projections
`TLM`, `TLR`, `TMR`, and `LMR`. Still, this board is **invalid**: it has only
73 distinct quadruples.

Its pattern counts follow a clean rule:

- Every pattern containing color 0 appears once.
- Among patterns using only colors 1 and 2, those with an even number of 2s
  appear twice.
- Among patterns using only colors 1 and 2, those with an odd number of 2s do
  not appear at all.

The sixteen non-unit patterns are:

| Absent | Doubled |
|---|---|
| `1112` | `1111` |
| `1121` | `1122` |
| `1211` | `1212` |
| `1222` | `1221` |
| `2111` | `2112` |
| `2122` | `2121` |
| `2212` | `2211` |
| `2221` | `2222` |

The marginal property follows immediately. Fix any three slots. If one of them
is 0, all three completions have count 1. Otherwise, the 0-completion has count
1 while the 1- and 2-completions have opposite parity (counts 0 and 2). Either
way, the three counts sum to 3.

The checker builds all placements from Cartesian coordinates, checks all 81
quadruple counts against this rule, and checks all 108 three-coordinate
marginal equations independently. The board and audit are saved in
[`exact_structure_counterexample.json`](exact_structure_counterexample.json).
[`MarginalCounterexample.lean`](../MarginalCounterexample.lean) formalizes
well-formedness, all 108 uniform triple counts, the doubled `1111` pattern, and
failure of the validity predicate in theorem
`TBoards.MarginalCounterexample.triple_marginals_insufficient`.

We found this witness with a prescribed-multiset variant of the fixed-prefix
search whose residual pattern capacities are 0, 1, or 2 instead of all 1 (all
three-coordinate margins, top-color quotas, and lower-pair flow balances still
hold, and the original solver is untouched). Reproduce the first witness with:

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_structure_trade_search.cpp -o /tmp/exact_structure_trade_search
/tmp/exact_structure_trade_search 100001001210200101000022122102110022 1 1 2 1
```

The prefix is the first cap of group 6 in `splice_extension.json`, and the run
output is saved in `exact_structure_trade_first.txt`. This finds a
counterexample to a relaxation, not a valid board or new lower bound.

## An exact replacement: sixteen four-coordinate conditions

**Proposition.** A ternary board is valid if and only if:

1. Every three-coordinate marginal equals 3 everywhere.
2. Each of the sixteen patterns in `{0, 1}^4` occurs exactly once.

Only sufficiency needs a proof. Induct on the number of 2s in a pattern. Zero
2s is condition 2. If a pattern has a 2, pick one such coordinate and fix the
other three; the three counts on that line sum to 3. Replacing that 2 with 0 or
1 gives two patterns with one fewer 2, each already known to have count 1, so
the original pattern must also have count 1. That covers all 81 patterns.

The counterexample above satisfies **15** of the 16 base conditions: inside
`{0, 1}^4`, only `1111` has count 2. So even on actual boards satisfying every
three-coordinate marginal, we cannot drop that last base condition.

We do not need all 108 marginal lines. For each pattern containing a 2, pick
the line that varies its **first** coordinate equal to 2 (earlier slots lie in
`{0, 1}`, later slots are free). That chooses

```
27 + 18 + 12 + 8 = 65
```

marginal lines, and the same induction uses only those 65. One of the 27
first-coordinate lines is redundant because all 27 sums add up to the total
number of placements (81), so any 26 sums of 3 force the last sum to be 3. That
leaves **64 selected marginal lines plus 16 base counts** (80 scalar conditions
in all).

For an arbitrary real 81-entry count table summing to 81, fixing all proper
marginals leaves a 16-dimensional space of four-way contrasts, matching the 16
base conditions. This gives an alternative exact encoding without claiming a
speedup or an evaluated ternary count.

[`ExactMarginals.lean`](../ExactMarginals.lean) formalizes the equivalence
for the 65 selected lines and 16 base counts and links it directly to board
validity in `TBoards.ExactMarginals.valid_iff_reduced`. Dropping the one
redundant line follows from the total-placement sum above.

## Why the binary implication is stronger

Let `C(p)` be the sixteen quadruple counts of a binary board. Uniform
three-coordinate marginals say

```
C(p) + C(p with coordinate i flipped) = 2
```

for every coordinate `i`, which forces

```
C(p) = 1 + s (-1)^(sum of the four bits),   s ∈ {-1,0,1}.
```

Here `s = 0` is validity. When `s = ±1`, every occurring T has fixed XOR parity
`e`, forcing

```
top = e XOR left XOR middle XOR right.
```

Then the nine bottom-row bits determine the whole board. The checker tests all
512 bottom rows for both parities (`e = 0` and `e = 1`). In all 1,024 cases,
some quadruple appears at least 3 times, contradicting a table whose nonzero
counts are all 2. So uniform three-coordinate marginals **do** force validity
for binary boards. A separate SAT check also returned UNSAT, though the direct
1,024-case check already settles it without trusting a SAT solver.

## The deterministic ternary relaxation is also impossible

Suppose a ternary count table with uniform three-coordinate marginals only
takes values 0 and 3. Then each lower triple `(l, m, r)` has one allowed top
color `t = f(l, m, r)`, and the other three marginals say `f` is bijective in
each argument when the other two are fixed (a ternary quasigroup of order 3).

Every such function is affine over `F_3`:

```
f(l,m,r) = a l + b m + c r + d,
where a,b,c ∈ {1,2} and d ∈ {0,1,2}.
```

To see why, note that in any order-3 Latin square the first row is an affine
permutation of `F_3`, and each other row must disagree with it everywhere, so
it is a shift by 1 or 2. Both shifts appear in either order, making every
order-3 Latin square affine with two nonzero slopes. Applying this to every
2D slice of `f` shows that the slope in each coordinate is constant globally,
so subtracting the three linear terms leaves a constant. The checker also
enumerates all 12 Latin squares and all 24 ternary quasigroups to confirm this
directly.

Under any of the 24 rules, the 19-cell bottom row fixes every upper cell.
[`exact_structure_ca.cpp`](exact_structure_ca.cpp) searches all 24 rules by
filling the bottom row left to right, computing newly forced upper cells
immediately, and pruning whenever a lower triple appears more than 3 times. At
a full board, 81 placements across 27 capacities of 3 force every lower triple
to appear exactly 3 times, and the nonzero slopes then guarantee all four
three-coordinate marginals.

All 24 searches finished with **zero solutions**, exploring roughly 2 to 3
million partial states per rule (see
[`exact_structure_ca_all.log`](exact_structure_ca_all.log)). This exhausts only
the affine subclass, not all ternary boards. Compile and run one rule with:

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_structure_ca.cpp -o /tmp/exact_structure_ca
/tmp/exact_structure_ca 3 2 2 2 0 60
```

The last argument is a time limit; only a `COMPLETE` output certifies
exhaustion.

One direct consequence: any invalid ternary board with uniform three-coordinate
marginals must have at least one quadruple with count **2**. If no entry is 2,
any entry equal to 1 forces the other two entries on every coordinate line
through it to sum to 2 within `{0, 1, 3}`, so they must both be 1, spreading
count 1 everywhere. If no entry is 1 either, every entry is 0 or 3, which is
the ruled-out quasigroup case. Every doubled entry also forces one 1 and one 0
on each coordinate line through it.

## Why the local output permutations do not directly give a BEST formula

On any valid board, each input triple `(t, l, m)` sees its three output colors
in some permutation order. Together with the 19 free boundary cells, those 27
permutations determine the row-major board.

This looks like a rotor assignment, but it is not a rotor walk on the 27
triples. After writing output `r`, the next triple is `(t_next, m, r)`, where
`t_next` comes from the row above rather than from `(t, l, m, r)`. Two valid
binary boards show this mismatch at row 3, column 0:

```text
A: 0 / 000 / 00111 / 1101011 / 111001000
B: 0 / 000 / 01001 / 1101111 / 001011000
```

Both see `0110` there, yet their next triples are `010` and `110`. The same
happens for ternary boards: published seeds 2 and 3 (0-based in
`sources/anc/certificates.json`) both see `1110` at row 7, column 3, then move
to `210` and `110`. The checker verifies all four boards and transitions.
Geometrically, two distinct T placements share at most two cells, so there is
no standard three-cell-overlap de Bruijn graph either.

There is an even sharper obstruction to a last-exit rule on the 27 local
permutations. In published seed 0, triple `000` has output order `012`.
Changing only that order to `102` (keeping its last output `2` and all other
rotors and boundary colors fixed) fails at row 3, column 2 by requesting a
fourth output from `000`. So fixing all local last exits does not make the
remaining rotor orders free.

The standard BEST theorem applies to a **fixed directed graph** with fixed edge
endpoints, counting Euler tours from spanning trees and local edge orders (see
Holroyd et al., *Chip-Firing and Rotor-Routing on Directed Graphs*, Corollary
4.10, [author-hosted paper](https://personal.math.ubc.ca/~holroyd/papers/sand.pdf)).
That pins down what is missing from this direct identification without ruling
out every conceivable larger graph reformulation.

## Antisymmetrizing the output orders introduces uncancelled signs

Two valid ternary boards share rows 4 through 9:

```text
222012012
00021112200
0010010022200
110202021201011
02121111210221022
2221101121221000202
```

Their upper rows are:

```text
A: 2 / 122 / 11011 / 1200012
B: 2 / 122 / 11012 / 1200011
```

They share all 19 free boundary colors and the entire bottom row, and their
local output orders match at every triple except `201`, where A uses `120` and
B uses `210` (opposite permutation parities). So the product of local
permutation signs is not constant even when all of that boundary data is fixed:
a determinant or alternating-tensor sum would suffer cancellation that cannot
be fixed by that boundary alone. The checker verifies both boards (taken from
`splice_witnesses.json`, group 6: two caps sharing one tail) and their single
rotor swap.

## All local linear boundary divergences are already accounted for

Pick a basis of functions on the three colors consisting of the constant
function and two mean-zero functions, and expand any function of the four T
slots in the resulting 81-element tensor basis. When summing over all 81
placements, interior cell terms can cancel only between supports that are
translates of one another carrying the same basis labels.

Among subsets of the T shape, only single cells and the two adjacent horizontal
pairs (`LM` and `MR`) have repeated translation types. Four singleton positions
give 3 differences for each of 2 mean-zero labels (6 dimensions), and `LM` vs.
`MR` gives 4 more dimensions. Every other subset has a unique translation type.
The space of universal local linear divergences therefore has dimension **10**,
and the bulk map has rank **71** (verified directly by the checker).

Those ten identities are spanned by the 8 independent lower-pair endpoint
balances and the 2 independent color-conservation equations equating the
bottom-row color counts to the 19 free boundary cells. So telescoping sums of
local linear observables give no new independent boundary equations (this does
not address nonlinear or nonlocal identities).

## Bounded SAT and swap experiments

Before finding the counterexample above, scanning 466,246 representatives (the
first cap paired with every tail across all four saved splice-witness files)
found no two-cell switch of the required kind; the multiset search succeeded by
letting the tail change more freely.

`exact_structure_marginals.py` holds the direct marginal SAT model. The binary
counterexample formula returned UNSAT. Two 90-second Glucose4 runs (one
unrestricted, one with six rows fixed) returned UNKNOWN; they are kept as
diagnostics now that the explicit ternary witness settles the question directly.

An initial CaDiCaL run ran past its intended limit because the installed PySAT
version did not support interrupting CaDiCaL. That process was stopped and
recorded as UNKNOWN. The script now allows only Glucose4 or Minisat22, checks
their interrupt API first, and passed its timeout smoke test with UNKNOWN. No
interrupted search is treated as an exhaustion or impossibility proof.
