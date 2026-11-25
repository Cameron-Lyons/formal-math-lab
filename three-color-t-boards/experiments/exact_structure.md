# Exact-count structure: a failed relaxation and an exact replacement

The unrestricted ternary count is not evaluated here. The main new result is
an explicit counterexample to replacing full T-pattern uniqueness by uniform
three-coordinate marginals. An exact replacement uses those marginals together
with only sixteen specified quadruple counts. The accompanying experiments also
rule out two direct applications of Euler-tour and determinant counting.

Run the independent finite checks with:

```sh
python experiments/exact_structure_check.py
```

## Uniform three-coordinate marginals do not suffice for ternary boards

This board has the usual row lengths 1,3,…,19:

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

Let `C(t,l,m,r)` count its ordered T patterns. Every one of the 27 triples
occurs exactly three times in **each** of the four three-coordinate
projections `TLM`, `TLR`, `TMR`, and `LMR`. Nevertheless this is **not a valid
T board**: it has only 73 distinct quadruples.

Its complete multiplicity rule is particularly simple:

- Every pattern containing color 0 occurs once.
- Among patterns using only 1 and 2, those with an even number of 2s occur twice.
- Among patterns using only 1 and 2, those with an odd number of 2s are absent.

The sixteen exceptions to multiplicity one are:

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

This rule immediately proves the marginal claim. Fix any three coordinates.
If one is 0, all three completions have count one. Otherwise the completion
using 0 has count one, while the completions using 1 and 2 have opposite
parities and counts zero and two. Their sum is always three.

The checker reconstructs placements from Cartesian coordinates, checks all
81 quadruple multiplicities against this rule, and independently checks all
108 three-coordinate marginal equations. The complete board and audit are in
[`exact_structure_counterexample.json`](exact_structure_counterexample.json).
[`MarginalCounterexample.lean`](../MarginalCounterexample.lean) formalizes
well-formedness, all 108 uniform triple counts, the doubled `1111` pattern,
and failure of the original validity predicate. Its theorem
`TBoards.MarginalCounterexample.triple_marginals_insufficient` states the
counterexample result.

Discovery used a prescribed-multiset variant of the existing fixed-prefix
search. Its residual pattern capacities are 0, 1, or 2, rather than all one;
all three-coordinate margins, including top-color quotas and lower-pair flow
balance, remain valid. The original solver is unchanged. Reproduce the first
witness with:

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_structure_trade_search.cpp -o /tmp/exact_structure_trade_search
/tmp/exact_structure_trade_search 100001001210200101000022122102110022 1 1 2 1
```

The prefix comes from `splice_extension.json`, group 6, first cap. The search
output is `exact_structure_trade_first.txt`. This experiment supplies a
counterexample to a relaxation, not a new valid-board lower bound.

## An exact replacement: sixteen four-coordinate conditions

**Proposition.** A ternary board is valid if and only if:

1. Every three-coordinate marginal is uniformly three.
2. Each of the sixteen patterns in `{0,1}^4` occurs exactly once.

Only sufficiency needs proof. Induct on the number of coordinates of a pattern
that equal 2. The case of no 2 is condition 2. For a pattern containing a 2,
choose such a coordinate and fix the other three. The three corresponding
counts sum to three. Replacing the chosen 2 by 0 or 1 gives two patterns with
one fewer 2, each already known to have count one. The original count is
therefore also one. This covers all 81 patterns.

The counterexample above satisfies **fifteen** of the sixteen base conditions:
among `{0,1}^4`, only `1111` has count two. Thus the last condition cannot simply
be dropped, even when all three-coordinate marginals are enforced on actual
boards.

There is no need to encode all 108 marginal equations. Select a line for each
pattern containing a 2 by varying its **first** coordinate equal to 2. Earlier
coordinates belong to `{0,1}` and later coordinates are arbitrary. This gives

```
27 + 18 + 12 + 8 = 65
```

selected marginal lines. The same induction uses only these lines. One of the
27 lines obtained by varying the first coordinate is redundant: all those
line sums together total the fixed number of placements, 81, so any 26 sums
of three force the remaining sum to be three. Thus **64 selected marginal
conditions plus 16 base counts** form an exact system of 80 scalar conditions.

For an arbitrary real 81-entry count table of fixed total 81, the proper
marginals leave a 16-dimensional space of four-way contrasts. This matches the
sixteen base values above. The replacement is an alternative exact encoding;
no runtime improvement or evaluated ternary count is claimed.

[`ExactMarginals.lean`](../ExactMarginals.lean) proves the general count-table
equivalence for the 65 selected lines and sixteen base counts. Its theorem
`TBoards.ExactMarginals.valid_iff_reduced` connects that system directly to
the original board-validity predicate. The further removal of one redundant
line is the total-count argument above.

## Why the binary implication is stronger

For a binary board let `C(p)` be its sixteen quadruple counts. Uniform
three-coordinate marginals mean

```
C(p) + C(p with coordinate i flipped) = 2
```

for every coordinate `i`. Consequently

```
C(p) = 1 + s (-1)^(sum of the four bits),   s ∈ {-1,0,1}.
```

The case `s=0` is validity. In either other case every occurring T has fixed
XOR parity `e`, so its top color is forced by

```
top = e XOR left XOR middle XOR right.
```

The bottom row of nine bits therefore determines the entire board. The
independent checker exhausts all 512 bottom rows for each parity. In every
case some quadruple occurs at least three times, whereas the proposed table
would require every occurring quadruple to occur exactly twice. Therefore
uniform three-coordinate marginals **do** imply full validity in the binary
case. An independently encoded SAT test also returned UNSAT for a binary
counterexample; the direct 1,024-case check is sufficient without trusting SAT.

## The deterministic ternary relaxation is also impossible

Suppose a uniform-three-marginal ternary count table has only entries 0 and 3.
For each lower triple there is a unique possible top color, defining
`t=f(l,m,r)`. The other three marginals say that `f` is bijective in each
argument with the other two held fixed: it is a ternary quasigroup of order 3.

Every such function is affine over `F_3`:

```
f(l,m,r) = a l + b m + c r + d,
where a,b,c ∈ {1,2} and d ∈ {0,1,2}.
```

Here is an elementary classification argument. In a Latin square of order 3,
the first row is an affine permutation of `F_3`. Each other row must be a
pointwise derangement of the first, hence its translation by 1 or by 2. The
two translations occur in either order, so every Latin square is affine with
two nonzero coefficients. Apply this to every two-dimensional slice of `f`.
The slope in any coordinate is independent of each other coordinate, hence
is constant globally. Subtracting the three linear terms leaves a constant.
The checker also enumerates all 12 Latin squares and all 24 ternary
quasigroups and verifies this classification directly.

For each of the 24 rules, the bottom row of nineteen colors determines every
upper cell. [`exact_structure_ca.cpp`](exact_structure_ca.cpp) exhausts this
class by assigning bottom cells from left to right and immediately deriving
all newly determined upper cells. Whenever a lower triple is completed its
count increases; a count exceeding three rejects the branch. At a complete
board, 81 placements with 27 capacities of three force every lower triple to
occur exactly three times. The nonzero coefficients then imply all four
three-coordinate marginals.

All 24 searches exhausted with **zero solutions**, visiting approximately
2–3 million partial states per rule. See
[`exact_structure_ca_all.log`](exact_structure_ca_all.log). These are exact
exhaustions of the affine subclass, not of all ternary boards. Compile and
run an individual rule with:

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_structure_ca.cpp -o /tmp/exact_structure_ca
/tmp/exact_structure_ca 3 2 2 2 0 60
```

The last argument is a time limit; the result must say `COMPLETE` to support
an exhaustion claim.

A useful consequence is that any nonvalid ternary board with uniform
three-coordinate marginals must have a quadruple occurring **exactly twice**.
Indeed, suppose there were no entry 2. An entry 1 forces the other two entries
on any coordinate line to be 1, since they must sum to two and belong to
`{0,1,3}`. Propagation forces the whole table to be one. If there is no entry
1 either, the table consists only of 0s and 3s, the excluded quasigroup case.
A doubled entry also forces a 1 and a 0 on each coordinate line through it.

## Why the local output permutations do not directly give a BEST formula

For a valid board, each triple `(t,l,m)` encounters its three outputs in some
order, a permutation of the palette. Together with the nineteen free boundary
colors, these 27 permutations determine the row-major construction.

This resembles a rotor order, but does not define a rotor walk on the 27
triples. After output `r`, the next triple is `(t_next,m,r)`. The next top
color is drawn from the previously generated row; it is not determined by
`(t,l,m,r)`. Two valid binary boards illustrate the failure at the same
position, row 3, column 0:

```text
A: 0 / 000 / 00111 / 1101011 / 111001000
B: 0 / 000 / 01001 / 1101111 / 001011000
```

Both encounter `0110` there, but their next local states are `010` and `110`.
The same obstruction occurs for ternary certificates: published seeds 2 and 3
(zero-based indices in `sources/anc/certificates.json`) both encounter `1110`
at row 7, column 3, but the next states are `210` and `110`, respectively.
The checker independently validates these boards and transitions.
Geometrically, two distinct T translates overlap in at most two cells, so
there is also no usual three-cell-overlap de Bruijn graph for these windows.

There is a sharper obstruction to a last-exit criterion on the 27 local
permutations. For published seed 0, the output order at triple `000` is
`012`. Change only that order to `102`, preserving its last output and every
other local order and boundary color. The modified construction fails at
row 3, column 2: it asks to use triple `000` for a fourth time. Thus fixing
all local last outputs does not make the remaining output orders free.

The standard BEST correspondence concerns a **fixed directed graph** with
fixed edge endpoints and counts Euler tours from spanning trees and local
edge orders. These hypotheses explain precisely what the proposed
identification lacks; they do not rule out every conceivable larger graph
transformation. See Holroyd et al., *Chip-Firing and Rotor-Routing on Directed
Graphs*, Corollary 4.10,
[author-hosted paper](https://personal.math.ubc.ca/~holroyd/papers/sand.pdf).

## Antisymmetrizing the output orders introduces uncancelled signs

Two valid ternary boards share these rows 4 through 9:

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

They have identical nineteen free boundary colors and identical bottom rows.
Their local output orders agree at every triple except `201`, where A has
`120` and B has `210`. These permutations have opposite parity. Therefore
the product of local permutation signs is not constant, even after fixing
that complete boundary data. A determinant or alternating-tensor count
would have cancellations; its sign cannot be corrected by this boundary
alone. The checker verifies both boards and the exact single-order difference.
They come from `splice_witnesses.json`, group 6, two caps sharing one tail.

## All local linear boundary divergences are already accounted for

Choose a basis of functions on the three colors consisting of the constant
function and two mean-zero functions. Expand an arbitrary function of the
four T slots in the resulting 81-element tensor basis. When summing its
translates, interior terms can cancel only between supports that are
translations of one another with the same basis labels.

Among subsets of the T, only singleton supports and the two adjacent
horizontal pairs have repeated translation types. Four singleton positions
give three differences for each of two labels, hence six dimensions. The
pair supports `LM` and `MR` give four more dimensions. All remaining supports
have unique translation type. Thus the space of universal local divergences
has dimension **ten**; the bulk map has rank **71**. The checker computes
these translation classes directly.

These ten identities are generated by the eight independent lower-pair
endpoint balances and two independent color-conservation identities equating
the bottom-row histogram with the nineteen free boundary colors. Consequently
this particular class of telescoping local observables cannot supply further
independent boundary equations. This statement concerns universal linear
local identities, not nonlinear constraints or nonlocal arguments.

## Bounded SAT and swap experiments

Before the explicit construction, a scan of 466,246 representatives (the first
cap with every tail in each of the four saved splice witness files) found no
two-cell switch of the required type. That negative result was limited to
those representatives. The successful multiset search allowed the tail to
change more extensively.

The direct marginal SAT model is in `exact_structure_marginals.py`. The binary
counterexample formula returned UNSAT. Two 90-second Glucose4 trials, one
unrestricted and one fixing six rows, returned UNKNOWN. These results are
preserved as diagnostics; the explicit ternary witness now settles the
relaxation question independently.

An initial CaDiCaL trial exceeded its intended limit because the installed
PySAT version does not support that solver's interruption method. The owned
process was terminated and recorded as UNKNOWN. The script now offers only
Glucose4 or Minisat22, probes their interrupt API, and the timeout smoke test
successfully returned UNKNOWN. None of the interrupted searches is treated
as an exhaustion or impossibility result.
