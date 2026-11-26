# Pattern-permutation signs: exact cancellation and limited correction obstructions

Assigning a sign to the permutation of the 81 T patterns cannot recover the
board count. The unrestricted signed sum is **exactly zero**, and both signs
still appear among lexicographically canonical `S₃×reflection` representatives.
These results rule out fixed-sign counting and the factorized sign corrections
below, though they do **not** rule out every possible determinant, Pfaffian, or
exterior-algebra construction.

## Fixed ordering and reflection

Order placements by lower row `r = 1, ..., 9`, then starting column
`j = 0, ..., 2r−2`. Order patterns lexicographically as `(t, l, m, o)` with
index `27t + 9l + 3m + o`. Every valid board induces a permutation of
`0, ..., 80`; write `ε(b)` for its sign.

A global swap of two colors fixes the single all-third-color pattern and pairs
up the other 80 patterns into 40 transpositions. That permutation is even, so
every global color permutation preserves `ε`.

Horizontal reflection swaps the left and right pattern slots, fixing 27 labels
and pairing the other 54 into 27 transpositions (label sign `−1`). On
placements, reflection reverses the nine rows of lengths `1, 3, ..., 17`, which
takes `0 + 1 + ... + 8 = 36` transpositions (placement sign `+1`). Combining
both gives

\[
\varepsilon(Rb)=-\varepsilon(b).
\]

Reflection therefore pairs every valid board with an opposite-sign partner, so
`Σ_valid b ε(b) = 0`, whereas valid boards exist so the unsigned count is
nonzero. Changing either fixed ordering only multiplies every sign by the same
global constant and leaves all obstructions unchanged.

## No factorized per-cell/color correction on the full set

First try a factorized sign `W(b) = κ ∏_v w[v, b_v]` with every factor in
`{±1}`. Let `C` be a cyclic color rotation, and for any valid board `b` take
the six boards

`b, Cb, C²b, Rb, CRb, C²Rb`.

Every cell-color pair appears twice across these six boards, so the product of
their six `W` weights is `+1`, while the product of their six permutation signs
is `−1`. They cannot all become positive. This is a universal six-board
identity.

The same obstruction holds for **arbitrary fixed nonzero real or complex cell
weights**. The product of `W` over the first cyclic triple equals its product
over the reflected triple: both equal `κ³ ∏_v ∏_c w[v, c]`. Because the two
triples have opposite products of permutation signs, the weighted terms cannot
all be positive real numbers or all equal the same nonzero real or complex
constant. (This uses equality of the two triple products directly, rather than
parity of occurrences.)

## A minimum-distance canonical pair

Entries **7 and 8** (0-based) of `extended_seeds.json` are already the
lexicographically smallest boards in their `S₃×reflection` orbits. Both share
the first nine rows:

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

They differ only at bottom-row columns 13 and 15 (swapping 0 and 1) and share
all 19 rotor-boundary colors `0000000011002122122`. So neither the rotor
boundary nor the entire nine-row cap determines `ε(b)`.

Hamming distance 2 is minimal between distinct valid boards: changing a single
cell alters the color count of every role containing that cell (every cell lies
in at least one role), while every valid board has 27 cells of each color in
every role.

A second pair in `extended_seeds.json`, entries **162 and 164**, also has
opposite signs while sharing both the 19 rotor-boundary colors and the **entire
bottom row**. They differ only at `(row6, column11)` and `(row8, column15)`;
their full rows are saved in the certificate. That rules out any sign
correction depending only on the rotor boundary and bottom row.

## Exact relation to local output-order signs

Let `g_i = (t_i, l_i, m_i)` be the sequence of input triples in placement
order, and let `ρ_g` be the permutation of output colors seen at triple `g`.
Splitting inversions by whether their input triples match or differ gives

\[
\varepsilon(b)=(-1)^{\operatorname{inv}(g_0,\ldots,g_{80})}
                  \prod_{g\in Q^3}\operatorname{sgn}(\rho_g),
\]

where equal triples do not add to the shuffle inversion count. How different
triples interleave matters.

Between entries 7 and 8, only rotor `200` changes (`201` to `210`) while both
shuffle signs stay `+1`. Between entries 162 and 164, both boards have
rotor-sign product `−1`, yet their shuffle signs differ. So even combining the
rotor-sign product with the boundary and bottom row still fails to determine
`ε`.

This also explains the earlier pair in `exact_structure.md`: those two
same-boundary, single-rotor-swap boards both have pattern sign **−1** because
the rotor-sign product and the shuffle sign both flip and cancel. That earlier
rotor-sign obstruction is distinct from a pattern-sign obstruction. Full rotor
orders plus boundary colors still determine the entire board, so we make no
impossibility claim for general functions of all that data.

## Factorized sign correction also fails on the canonical set

The saved certificate lists **56 distinct canonical valid boards**. Across
those 56 boards, every color occurs an even number of times at each of the 100
cells, yet 31 of the 56 boards have negative pattern sign.

Equivalently, represent a factorized `{±1}` correction by 301 Boolean unknowns
(one global constant plus 300 cell-color indicators). XORing the 56 equations
gives 0 on the left and 1 on the sign side. So no product of per-cell/color
`{±1}` weights (and hence no nonzero real weights, by taking their signs) can
correct all canonical boards. This 56-board certificate makes **no claim about
arbitrary complex phases** and is not claimed to be minimal.

## Reproduction and scope

[exact_sign_math_certificate.json](exact_sign_math_certificate.json) embeds all
boards used here, their signs, their rotor tables, and the 56-board XOR
certificate, so checking does not depend on external board files:

```sh
python experiments/exact_sign_math.py --check
```

The checker verifies board validity, recomputes every sign by both inversion
parity and cycle count, verifies canonicalization, and checks the XOR both as a
301-bit indicator identity and by direct cell-color counts. Results are saved
in [exact_sign_math_check_results.json](exact_sign_math_check_results.json).
Running without `--check` rebuilds the same witnesses from the source board
files. No new board search or full counting was performed.
