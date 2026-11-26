# Source analysis of the third degree-four failure

The rounded-capacity full reduced F2 trial passed the earlier allocation boundary and finished a second degree-4 round. It then printed a matrix with 26,569 rows, 2,626,958 columns, and 0.13% density before crashing with signal 11. The parent's second debugger replay **confirmed a null output-row allocation followed by a write through that null pointer**. No solver, source patch, or new build was run for this note.

Inspected tree: `exact_msolve_rounded_promotion_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2`. Terminal artifacts: `exact_msolve_full_prime2_reduced_all_rounded.log` and `.json`. No basis or count was produced.

## Execution path and capacity independence

At characteristic 2, `meta_data.c:39` chooses 8-bit coefficient storage. Option `-l2` dispatches at `io.c:899` to `exact_sparse_linear_algebra_ff_8` (`la_ff_8.c:2209`), which calls `exact_sparse_reduced_echelon_form_ff_8` (`la_ff_8.c:1321`).

`f4.c:430-432` converts symbolic hashes to column indices, sorts the reducer-row pointer list, and runs linear algebra. The matrix dimensions and density print near the end of `convert.c:426`, after row entries are remapped. From the log alone, the crash could sit anywhere after conversion, including `qsort` at `order.c:120`, until a backtrace confirms entry into linear algebra.

Nothing in `la_ff_8.c` reads a hash table or touches `esz`, `hsz`, `ev`, `hmap`, `bs->ht`, or `tbr->ht`; it operates strictly on column indices and coefficient arrays. The row-sort comparator reads only pivot and length metadata. Non-power-of-two basis capacity is never accessed here, ruling out a direct capacity assumption bug at this stage (though not earlier memory corruption by itself).

## Unchecked allocations in `src/neogb/la_ff_8.c`

None of the following allocations checks for null before writing, so an allocation failure causes a signal with no error message:

| Allocation | Size for the logged matrix | First relevant use |
| --- | --- | --- |
| Line 2223: `realloc(mat->cf_8, mat->nr*sizeof(cf8_t*))` | 212,552 bytes (about 0.203 MiB) | Coefficient-pointer writes at line 1351. |
| Line 1341: `calloc(ncols,sizeof(hm_t*))` for `pivs` | 21,015,664 bytes (20.042 MiB) | Immediate `memcpy` at line 1343. |
| Line 1359: `malloc(ncols*nthrds*sizeof(int64_t))` for `dr` | 21,015,664 bytes (20.042 MiB with 1 thread) | `memset(drl,...)` at line 1377. |
| Lines 542-543: output monomial row and coefficient array | `4*(k+OFFSET)` and `k` bytes for support size `k` (at most about 10.021 MiB and 2.505 MiB) | `rs[j]` / `cf[j]` writes at lines 548-549, then row metadata. |
| Lines 1452-1453: dense workspace and output-row pointer reallocations | Workspace about 20.042 MiB; pointer array `8*ncr`, also near 20 MiB | Interreduction `memset` at line 1461 and `mat->tr[npivs++]` at line 1482. |

Notice that line 1453 sizes the pointer array by `ncr` (all nonpivot columns) even though the selected batch has about 17 candidate new rows, making it an oversize allocation (though not shown to be the crashing one). A null return from the row reducer on a zero reduction is normal; a failed output allocation crashes instead because the reducer dereferences the pointer before returning.

The final shrink at line 1487 is also unchecked, though it requests only the small pivot count and is far less likely to fail (and a zero-length shrink can legitimately return null when there are no new pivots).

## Memory scale

Before this round, the 96-variable basis hash at capacity 2,162,688 used 481.625 MiB in its principal arrays, and the symbolic hash still used a power-of-two capacity of 4,194,304 (about 904 MiB), totaling 1,385.625 MiB before matrix rows, basis polynomials, and LA workspaces.

The printed 0.13% density is rounded. At face value it corresponds to about 346 MiB in 4-byte matrix column indices alone, with rounding allowing roughly 333 to 359 MiB. Adding matrix metadata, stored basis data, and output rows brings total usage close to the 2-GiB address-space cap, where two extra 20-MiB workspaces can tip it over.

A null destination in `memcpy`, `memset`, or row output points to an unchecked allocation failure, whereas a nonnull out-of-range pointer would point elsewhere. Either way, the run stays incomplete with no board count.

## Debugger confirmation: null output-row allocation

The parent's first bounded debugger replay stopped in `reduce_dense_row_by_known_pivots_sparse_ff_8.isra.0` at static offset `0x30fcd`. Disassembly maps that instruction to source line 548 (`rs[j] = (hm_t)i`), placing the crash inside the output-row builder rather than row sorting or hash access.

In the disassembly:

- At `0x30f91`, `malloc` allocates `4*(k+6)` bytes for the monomial row (line 542) and saves the return value in `R12` at `0x30f9a`, unchanged until the fault.
- At `0x30f9d`, the coefficient array allocation (line 543) returns into `RDI`.
- The faulting instruction is `mov %r13d,0x18(%r12,%rsi,4)`, where `R12` is `row`, `RSI` is `j`, `R13d` is `i`, and the `0x18` offset skips the 6 four-byte metadata slots.

The second replay (`exact_msolve_full_prime2_reduced_all_rounded_debug_registers.log`) stopped at the exact same instruction with `R12 = 0`, `RSI = 0`, nonzero `RDI`, and fault address `0x18`, using the same input, executable hashes, and 2-GiB cap. Because `R12` is the untouched `malloc` return, this proves the monomial-row allocation returned null while the smaller coefficient allocation succeeded.

The support size `k` was not captured. Neither its likely stack slot at `RSP+0x2c` nor the formula `4*(k+6)` yields a measured request size, so no failed byte count is claimed. The disassembly is saved in `exact_msolve_la_fault_disassembly.txt`.
