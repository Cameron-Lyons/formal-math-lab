# Characteristic-two matrix memory assessment

Pinned msolve v0.11.0 has no dedicated GF2 or bitset matrix kernel. Its finite-field linear algebra lives in `la_ff_8.c`, `la_ff_16.c`, and `la_ff_32.c` (plus rational arithmetic), and characteristic 2 uses the generic 8-bit coefficient path (`meta_data.c` picks coefficient width; `io.c` dispatches exact option 2). The bundled tutorial marks option 2 as exact and option 44 as probabilistic, and the source also includes exact sparse-dense option 1.

Option 1 (`sparse_AB_CD_linear_algebra_ff_8`) already frees old reducer rows before creating sparse outputs. Even so, it still allocates an 8-byte dense workspace per column, a full-column pointer table, and byte-dense residual rows, so it does not use F2 bit packing. It is a valid unmodified option, though no full option-1 run was tried here.

The approved fifth build targets the exact option-2 path instead: keep old reducers sparse, hold only the workspace and new pivots as bitsets, and free old reducer rows before building standard sparse outputs. See `exact_msolve_f2_bitset_tools/README.md` for invariants, scope, ownership, hashes, and small-fixture tests. All polynomial math stays ordinary characteristic-2 arithmetic with no Boolean variable relations added.

At 2,626,958 columns, a packed bitset workspace uses 328,376 bytes instead of 21,015,664 bytes. The new kernel also eliminates the 21,015,664-byte pivot pointer table and the large temporary output pointer array used during interreduction. The main expected saving comes from delaying sparse output allocation until after old reducer supports are freed, though the persistent basis and hash tables remain. These size numbers do not guarantee a speedup or completion on the full board.

Other shortcuts do not fit this matrix:

- 16-bit sparse column indices cannot index 2.6 million columns (which need 22 bits).
- A 1-byte XOR workspace alone would save about 17.54 MiB while leaving the sparse-output allocation peak intact.
- Packing every old row would waste memory at the measured 0.13% density, so the fifth build keeps the old block sparse.
