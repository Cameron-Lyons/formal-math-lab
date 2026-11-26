# Independent serial F2 bitset review

Review complete: no correctness issues were found in the frozen corrected kernel. This review ran no full T-board solve, so it validates the guarded kernel and small complete bases without establishing a full board count or predicting full-run resource needs.

- Candidate executable SHA-256: `78e65a3c746a036d12ac67d8c332a9afd2101746eee3b850d4a2ecb5e696f502`
- Kernel SHA-256: `194f90bf81adf33cbc006933367056cffce4c2be2fa9210886596b89593928eb`
- Patch SHA-256: `3868e06ffa3fba3f1ff30aab9693070489fdc533a683df6e8e6d8ad7c92b3a8b`
- Prior rounded-allocation executable SHA-256: `cebd842aa617f09725a1f5429ebc822da238563f142b14993cccb85312d1874c`

## Source argument and boundary ownership

The dispatch gate restricts the bitset path to characteristic 2, exact sparse option 2, one thread, no tracer, no normal-form mode, no final-reduction mode, no elimination variables, and basis export. All other modes use the existing kernel. The routine rechecks these rules and requires the known pivot block to occupy columns `0` through `ncl - 1`, with every coefficient equal to 1.

Each lower row is reduced from left to right. Because every reducer starts at its pivot column, XORing with a reducer never modifies an earlier column. The surviving nonzero rows therefore form independent new pivots spanning the quotient row space modulo the old pivots. Interreducing in descending pivot order eliminates every other new pivot column, carrying out standard exact Gaussian elimination over F2.

The first draft assumed each sparse row tail was sorted. An owner test revealed that the upstream converter places the leading column first but can leave tail columns in arbitrary order; that draft failed closed with no accepted basis. The frozen version checks the leading column, uniqueness, valid column bounds, and unit coefficients while allowing arbitrary tail order. The tests below include 961 unsorted-tail matrices.

Ownership stays clean across the boundary:

- Borrowed coefficient arrays stay basis-owned and are never edited or freed.
- Lower sparse rows are freed after copying into the bitset workspace.
- Old reducer sparse rows are all freed before new sparse rows and coefficient arrays are allocated.
- The lower pointer container is replaced after forward elimination.
- New rows keep their original lower-row `BINDEX` and `MULT` metadata, with `COEFFS` set to the original lower-row position (matching the generic serial kernel).
- Matrix-to-basis conversion takes ownership of the output sparse rows and coefficient arrays, sets `DEG` as before, and leaves `clear_matrix` to free only the pointer containers.

Every checked allocation failure exits nonzero rather than returning a partial basis. Bit-packing matrix coefficients changes nothing about the polynomial ring itself: the ordinary `x_i^3 + 1` domain equations stay untouched with no Boolean variable identities added.

## Independent checks

`exact_msolve_f2_matrix_review.py` compiles a harness that directly includes the frozen kernel C source and compares it against an independent Python Gauss-Jordan oracle built with sets. It verifies exact reduced supports and original lower-row metadata, including reversed borrowed coefficient slots.

Results in `exact_msolve_f2_matrix_review_results.json`:

- 1,039 matrices, 11,594 new pivots, and 57 zero-output cases.
- Covers empty matrices, full rank, dependencies, duplicate rows, unsorted tails, dense and sparse supports, and word boundaries at 63/64/65, 127/128/129, and larger widths.
- Confirms old reducers are freed before output materialization and borrowed arrays stay untouched.
- Injects failures at all 19 allocation sites on a nontrivial path; all exit nonzero cleanly.
- Rejects all 16 invalid input/mode cases cleanly.
- Clean under AddressSanitizer and UndefinedBehaviorSanitizer.

`exact_msolve_f2_basis_review.py` checks 12 complete F2 ideals against both the prior executable and an independent Python Buchberger solver. All 24 full-basis exports match the Python reference and are byte-identical across binaries, exercising 33 bitset matrix rounds. Fixtures include coupled cubic roots, dense equations, Frobenius partners, an inconsistent ideal, and a nonradical ideal: three independent cubics give dimension 27, the quadratic coefficient-field fixture gives dimension 2, and `(x1^3, x2^2)` gives dimension 6, catching any accidental Boolean reduction or lost multiplicity.

An early basis test used a 1-GiB address-space cap, under which the prior baseline crashed before finishing a basis. A targeted check reproduced that failure at 1 GiB and passed at the standard 2-GiB cap. All recorded comparisons use 2 GiB, and the early 1-GiB crash artifacts are kept in `exact_msolve_f2_basis_review_runs` (uncounted as passing runs; they reflect the tighter memory cap rather than a regression).

The build owner separately recorded 18 complete `-g 1` / `-g 2` comparisons (including a saved six-completion fiber) and 4 fallback mode tests in `exact_msolve_f2_bitset_tools/validation.json` and `mode_validation.json`.

The frozen corrected executable hash is now allowlisted in `exact_msolve_cap_split.py`, while the failed draft hash is excluded. Full count aggregation still requires all 10 completed cap results and full per-artifact auditing.
