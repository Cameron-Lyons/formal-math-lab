# Source analysis of the third degree-four failure

The rounded-capacity full reduced F2 trial completed the previous allocation
boundary and a second degree-four round. It then printed a matrix with
26,569 rows, 2,626,958 columns and 0.13% density before terminating with
signal 11. The parent's second debugger reproduction now **confirms a null
output-row allocation followed by a write through that null pointer**. No solver,
source patch or new build was run for this assessment.

The inspected tree is
`exact_msolve_rounded_promotion_tools/msolve-cc044551f8e202d00691990fd3fd0b1226a88ea2`.
The terminal artifacts are `exact_msolve_full_prime2_reduced_all_rounded.log`
and `.json`. There is no completed basis or count.

## Execution path and capacity independence

At field characteristic two, `meta_data.c:39` selects eight-bit coefficient
storage. Option `-l2` dispatches in `io.c:899` to
`exact_sparse_linear_algebra_ff_8` (`la_ff_8.c:2209`), then
`exact_sparse_reduced_echelon_form_ff_8` (`la_ff_8.c:1321`).

`f4.c:430–432` first converts symbolic hashes into column indices, sorts the
reducer-row pointer list, and invokes linear algebra. The dimension/density
message is printed near the end of `convert.c:426`, after all row entries
have been remapped. The message alone therefore places the crash after
conversion but leaves the intervening `order.c:120` `qsort` possible until a
backtrace confirms entry into linear algebra.

The entire `la_ff_8.c` file contains no access to a hash table, `esz`, `hsz`,
`ev`, `hmap`, `bs->ht` or `tbr->ht`. It works with matrix column indices and
coefficient arrays. The row-sort comparator likewise reads only row pivot
and length metadata. Non-power-of-two basis capacity is not read directly
at this stage. This excludes a direct capacity-assumption dependency here;
it does not by itself rule out earlier corruption.

## Concrete unchecked allocations

All line references below are within `src/neogb/la_ff_8.c` in the pinned
tree. These allocations have no null check before use and can produce a
signal without an allocation diagnostic.

| Allocation | Size for the logged matrix | First relevant use |
| --- | --- | --- |
| Line 2223: `realloc(mat->cf_8, mat->nr*sizeof(cf8_t*))` | 212,552 bytes, about 0.203 MiB | Coefficient-pointer writes at line 1351. |
| Line 1341: `calloc(ncols,sizeof(hm_t*))` for `pivs` | 21,015,664 bytes, 20.042 MiB | Immediate `memcpy` at line 1343. |
| Line 1359: `malloc(ncols*nthrds*sizeof(int64_t))` for `dr` | 21,015,664 bytes, 20.042 MiB with one thread | `memset(drl,...)` at line 1377. |
| Lines 542–543: output monomial row and coefficient array | `4*(k+OFFSET)` and `k` bytes, where `k` is output support; at most roughly 10.021 MiB and 2.505 MiB | `rs[j]` / `cf[j]` writes at lines 548–549, then row metadata. |
| Lines 1452–1453: dense workspace and output-row pointer reallocations | Workspace about 20.042 MiB; pointer array `8*ncr`, also near 20 MiB | Interreduction `memset` at line 1461 and `mat->tr[npivs++]` at line 1482. |

The last pointer-array reservation uses the number of nonpivot columns,
although the logged selected batch has about 17 candidate new rows. This is
an observable potentially excessive allocation, but there is no evidence
yet that it is the failing one. The zero-reduction/null-row return from the
row reducer is normal; a failed output allocation is different because the
routine writes through it before returning.

The final shrink at line 1487 is also unchecked, although requesting only
the actual small number of pivots makes it a less likely allocation-failure
site than the large allocations above. A zero-length shrink can legitimately
return null when there are no new pivots.

## Memory scale and interpretation

Before this round, the 96-variable basis hash at capacity 2,162,688 reserves
481.625 MiB in its principal arrays. The symbolic hash still uses power-of-two
capacity 4,194,304, about 904 MiB. Together those arrays account for about
1,385.625 MiB before matrix rows, stored basis polynomials and linear-algebra
workspace.

The printed density is rounded. Taking 0.13% at face value suggests about
346 MiB in four-byte matrix column indices alone; rounding permits roughly
333–359 MiB. This is an estimate, not a measured allocation total. Matrix
metadata, stored basis coefficients/monomials and output rows add further
memory. Two additional 20 MiB workspaces can therefore matter under a 2 GiB
address-space limit.

A debugger null destination at the immediate `memcpy`, `memset` or row-build
write would support unchecked allocation failure. A nonnull out-of-range
matrix row or coefficient pointer would require a different investigation.
Preserve the terminal status as incomplete/error in either case; no output
count follows from this crash.

## Debugger reproductions: confirmed null row allocation

The parent's first bounded debugger reproduction stopped in
`reduce_dense_row_by_known_pivots_sparse_ff_8.isra.0` at static executable
offset `0x30fcd`. Disassembly of the preserved executable maps this exactly
to source line 548, `rs[j] = (hm_t)i`. This confirms the crash is inside the
output-row builder, not row sorting or a direct hash-capacity access.

At `0x30f91`, `malloc` receives `4*(k+6)` bytes for the monomial row from
line 542. At `0x30f9a`, its return value is saved in `R12` and is not changed
again before the fault. The coefficient allocation from line 543 occurs at
`0x30f9d`, with its return later held in `RDI`. The faulting instruction is
`mov %r13d,0x18(%r12,%rsi,4)`: `R12=row`, `RSI=j`, `R13d=i`, and six
four-byte metadata slots account for displacement `0x18`.

The parent's second bounded reproduction, saved in
`exact_msolve_full_prime2_reduced_all_rounded_debug_registers.log`, stopped
at the same instruction with `R12=0`, `RSI=0`, nonzero `RDI`, and signal
fault address `0x18`. Because `R12` is the unchanged return from the row
`malloc`, this establishes that the row allocation returned null and the
first index write dereferenced it. The smaller coefficient allocation had
returned a nonnull pointer. The replay retained the same input/executable
hashes and 2 GiB address-space cap.

The support size `k` was not captured. Its possible stack location at
`RSP+0x2c` and the allocation formula `4*(k+6)` do not establish an observed
request size; no specific failed byte count is claimed. The corresponding
disassembly is preserved in `exact_msolve_la_fault_disassembly.txt`.
