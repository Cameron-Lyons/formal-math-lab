# Pattern-permutation signs: exact cancellation and limited correction obstructions

The ordinary board count cannot be recovered by assigning a common sign to
the permutation of the 81 T patterns. The unrestricted signed count is
**exactly zero**, and both signs remain among lexicographically canonical
`S₃×reflection` representatives. These findings rule out this fixed-sign
approach and the factorized corrections below, **not every determinant,
Pfaffian, or exterior-algebra construction**.

## Fixed ordering and reflection

Order placements by lower row `r=1,…,9`, then starting column
`j=0,…,2r−2`. Order patterns lexicographically as `(t,l,m,o)`, with index
`27t+9l+3m+o`. A valid board defines a permutation of `0,…,80`; denote its
sign by `ε(b)`.

A global palette transposition fixes only the all-third-color label and
exchanges the other 80 labels in 40 pairs. Its label permutation is even;
therefore every global palette permutation preserves `ε`.

Reflection swaps the left and right pattern coordinates. It fixes 27 labels
and exchanges the remaining 54 in 27 pairs, hence has label sign −1.
Reflection on the placement set reverses rows of lengths `1,3,…,17`, giving
`0+1+…+8=36` transpositions, hence placement sign +1. Consequently

\[
\varepsilon(Rb)=-\varepsilon(b).
\]

Reflection therefore pairs every valid board with an opposite-sign board,
and `Σ_valid b ε(b)=0`. The existence of valid certificates makes this
different from the nonzero ordinary count. Changing either fixed ordering
only multiplies every sign by the same constant and does not remove these
obstructions.

## No factorized per-cell/color correction on the full set

First consider signs `W(b)=κ∏_v w[v,b_v]`, with all factors in `{±1}`. Let `C`
be a cyclic palette rotation. For any valid board take

`b, Cb, C²b, Rb, CRb, C²Rb`.

Each cell/color appears exactly twice across these six boards. Thus the
product of their corrections is +1, while the product of their permutation
signs is −1. They cannot all become positive. This is a universal six-board
identity, not a statistical inconsistency.

The obstruction extends to **arbitrary fixed nonzero real or complex cell
weights**. The product of `W` over the first cyclic triple equals its product
over the reflected triple: both are
`κ³∏_v∏_c w[v,c]`. The products of the three permutation signs are opposite.
Hence the corrected contributions cannot all be positive real numbers, nor
all equal the same nonzero real or complex constant. This extension uses
equality of the two triple products, not merely an even-incidence argument.

## A minimum-distance canonical pair

Existing `extended_seeds.json` entries **7 and 8** (zero-based) are already
the lexicographically least members of their complete `S₃×reflection` orbits.
They share these first nine rows:

```text
0
000
00100
0020110
012021022
10110211112
0202221112200
122221012002201
21201221011212121
```

Their bottom rows are:

```text
A: 2202001021100001002    sign −1; 1215 inversions
B: 2202001021100100002    sign +1; 1218 inversions
```

Only bottom-row columns 13 and 15 differ, exchanging zero and one. Their 19
rotor-boundary colors are identical: `0000000011002122122`. Thus sign is not
determined by that boundary, or even by the entire first-nine-row cap.

The Hamming distance two is minimal among distinct valid boards. A one-cell
recoloring would change a unary color histogram in a role containing that
cell, whereas every valid board has exactly 27 occurrences of each color in
each role. Every board cell belongs to at least one placement role.

A second existing pair, entries **162 and 164**, has opposite signs while
sharing both the 19 rotor-boundary colors and the **entire bottom row**.
They differ only at `(row6,column11)` and `(row8,column15)`. Their full rows
are embedded in the certificate. This rules out correction by those combined
boundary data alone.

## Exact relation to local output-order signs

Let `g_i=(t_i,l_i,m_i)` be the sequence of local input triples in placement
order, and let `ρ_g` be the permutation of right colors encountered at triple
`g`. Counting inversions according to whether their input triples differ gives

\[
\varepsilon(b)=(-1)^{\operatorname{inv}(g_0,\ldots,g_{80})}
                  \prod_{g\in Q^3}\operatorname{sgn}(\rho_g),
\]

where equal triples do not contribute to the shuffle inversion count.
The interleaving of different triples matters.

For entries 7/8, only rotor `200` changes, from `201` to `210`, and both
shuffle signs are +1. For entries 162/164, the rotor-sign product is −1 for
both, but the shuffle signs differ. Hence even the local rotor-sign product
plus the shared boundary/bottom data does not determine `ε`.

This also clarifies the earlier example in `exact_structure.md`: its
same-boundary, single-rotor-swap boards both have pattern sign **−1**. The
rotor-sign product and shuffle sign both flip there, cancelling each other.
The prior rotor-sign obstruction must not be mistaken for a pattern-sign
obstruction. Full rotor orders plus boundary data still determine the board;
no impossibility claim is made about arbitrary functions of all those data.

## Factorized sign correction also fails on the canonical set

The saved certificate contains **56 distinct canonical valid boards**. At
each of the 100 cells, each color occurs an even number of times across the
56 boards, but 31 of their pattern signs are negative.

Equivalently, represent a proposed correction by Boolean unknowns for a
constant and all 300 cell/color indicators. XORing these 56 equations gives
zero on the coefficient side and one on the required sign side. Therefore
no fixed product of per-cell/color `{±1}` weights corrects every canonical
term. The same conclusion holds for nonzero real weights by taking their
signs. This canonical-set certificate makes **no corresponding claim for
arbitrary complex phases**. It is not asserted to be a smallest certificate.

## Reproduction and scope

[exact_sign_math_certificate.json](exact_sign_math_certificate.json) embeds
all boards used above, their signs, rotor data, and the explicit 56-board XOR
certificate. Verification does not depend on the source board files:

```sh
python experiments/exact_sign_math.py --check
```

The checker verifies validity, computes every sign independently by inversion
parity and cycle count, verifies canonicalization, and checks the XOR both as
a 301-bit indicator identity and by direct cell/color counts. Results are in
[exact_sign_math_check_results.json](exact_sign_math_check_results.json).
Running without `--check` reconstructs the same selected witnesses from
existing source certificates. No new-board search or full counting was done.
