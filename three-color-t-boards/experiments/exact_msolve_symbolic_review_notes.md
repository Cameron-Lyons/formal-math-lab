# Independent review of symbolic row reservation

The seventh build passes independent review. Executable SHA-256: `a8192deffde5d6dbc9b5abfdfcc5330bfb4553ba88361cd1d86b2d6492919f6a`; patch SHA-256: `11af8d44ef40a0fc51e91bdf24bed6f666b1d6870b2799020a558d4dcbdbf682`. No full board solve was run here, and these checks do not prove a full solve will fit in memory.

Comparing the C source tree against build 6b shows only `hash.c` and `symbol.c` changed; the other 59 C files are identical. In `symbol.c`, the only edits are three pre-reservation calls right before the unchanged matrix-row constructor (two in pair selection, one in reducer discovery).

A source row of length `L` inserts at most `L` new symbolic monomials, so reserving `eld + L + 1` makes the legacy `eld + L >= esz` growth check false even at the exact boundary. Small requests grow geometrically, while larger requests round up to a 65,536-entry multiple. The shared allocator verifies the sum, capacity limits, power-of-two bucket load invariant, allocation size products, and every allocation result. Basis promotion calls the same allocator with its fixed 65,536 quantum. Live exponent IDs, `hd` metadata (including symbolic `idx`), and insertion order all survive rehashing.

Pointer lifetimes stay valid at all three sites: the multiplier vector is already copied onto the stack, pair selection borrows source exponents from the separate basis table, and reducer discovery copies symbolic metadata by value and finishes reading its borrowed symbolic exponent pointer before reserving (reloading `sht->hd` through `sht` afterwards). The row constructor reads basis exponents and the stack multiplier, so no stale pointer is ever dereferenced.

The mode gate allows only ordinary serial exact sparse basis export over F2 or F3, outside tracing, normal-form, final-reduction, and elimination modes; other modes return before allocating. Allowing non-power-of-two symbolic capacities of at least 2,048 during staging is safe because staging indexes exponent slots linearly via the full inverse map rather than bit masking. Buckets remain powers of two, capacities at least 2,048 reset to 2,048, smaller capacities must still be powers of two, and borrowed arrays and scalars stay untouched.

## Independent checks

- **Extracted helper audit (`exact_msolve_symbolic_review.py` and `exact_msolve_symbolic_review_results.json`)**: tests actual reservation, support, and staging code against a linear monomial reference under ASan and UBSan:
  - 1,200 mapping/support cases (17 non-power-of-two stages, 3 zero-missing spare-boundary stages).
  - 8 row-capacity boundaries, 8 disabled-mode cases, 10 promotion-path and 4 symbolic-row allocation failures.
  - 13 invalid staging layouts, 9 invalid reservation cases, and 3 large-capacity arithmetic plans that deliberately fail at the first allocation after logging the target.
  - One initial reviewer fixture asked for row length 0 while expecting a failure; changing it to length 1 fixed the test with no owner source changes needed. All final runs are sanitizer-clean.
- **Basis review (`exact_msolve_symbolic_basis_review.py` and `exact_msolve_symbolic_basis_review_results.json`)**: 24 complete ideals (12 in F2, 12 in F3) yield 48 full-basis exports byte-identical to build 6b and matching an independent Python Buchberger solver, exercising 22 F2 and 24 F3 symbolic reservations and 3 staging rounds per field across field domains, coupled equations, nonradical ideals, extension roots, and a unit ideal.

## Owner checks (separately attributed)

We also read the owner's `exact_msolve_symbolic_reserve_tools/helper_check.json` and `validation.json`. Those separate artifacts report 49 prior upstream promotion cases, 4 translated/untranslated row-constructor comparisons at 120,001 live entries and 30,000 source terms (capacity 196,608 vs. 262,144, followed by non-power staging and lookup/insert/clean/legacy growth/copy/reinit/reset), 8 fallback gates, 7 capacity boundaries, 4 allocator failures under sanitizers, and 24 complete basis comparisons.
