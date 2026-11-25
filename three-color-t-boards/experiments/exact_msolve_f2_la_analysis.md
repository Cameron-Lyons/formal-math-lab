# Characteristic-two matrix memory assessment

Pinned msolve v0.11.0 has no separate GF2/bitset matrix kernel. Its finite-field
implementations are `la_ff_8.c`, `la_ff_16.c`, `la_ff_32.c` and rational
arithmetic; characteristic two selects the generic eight-bit coefficient
path (`meta_data.c`, finite-field width selection; `io.c`, exact option two
dispatch). The official bundled tutorial identifies option two as exact
and option 44 as probabilistic. The source also provides exact sparse-dense
option one.

Option one's `sparse_AB_CD_linear_algebra_ff_8` already delays sparse output
until old reducer rows are freed. It still uses an eight-byte dense
workspace per column and a full-column pointer table, and stores residual
rows as byte-dense arrays. It is a plausible unmodified alternative, but
does not exploit F2 packing. No full option-one run was performed here.

The approved fifth build targets the existing exact option-two boundary:
retain sparse old reducers, keep only new pivots and workspace as bitsets,
then free old reducer rows before constructing conventional sparse outputs.
See `exact_msolve_f2_bitset_tools/README.md` for invariants, scope, allocation
ownership, frozen hashes and small validation. The mathematics is ordinary
polynomial arithmetic with coefficients in F2; no Boolean variable relation
is introduced.

At 2,626,958 columns the packed workspace is 328,376 bytes, instead of
21,015,664. The new implementation also avoids the generic 21,015,664-byte
pivot pointer table and the interreduction's large temporary output pointer
array. The intended larger saving is delayed sparse output allocation while
old reducer supports are still present. It cannot remove the eventual
sparse basis/hash cost. No speedup or completion claim for the full board
follows from these size calculations.

Sixteen-bit sparse column indices are not viable for the observed matrix:
2.6 million columns need 22 bits. A one-byte XOR workspace alone would save
about 17.54 MiB but leave the actual sparse-output allocation peak in place.
Packing every old row would also be counterproductive at the observed
0.13% density; the fifth build keeps that block sparse.
