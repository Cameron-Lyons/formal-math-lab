# Independent serial F2 bitset review

Review complete: no correctness issue found in the frozen corrected kernel.
No full T-board solve was run by this reviewer. The evidence validates the
guarded arithmetic kernel and small complete bases; it does not establish a
full board count or predict the resources needed for one.

- Candidate executable SHA256:
  `78e65a3c746a036d12ac67d8c332a9afd2101746eee3b850d4a2ecb5e696f502`.
- Kernel SHA256:
  `194f90bf81adf33cbc006933367056cffce4c2be2fa9210886596b89593928eb`.
- Patch SHA256:
  `3868e06ffa3fba3f1ff30aab9693070489fdc533a683df6e8e6d8ad7c92b3a8b`.
- Prior rounded-allocation executable:
  `cebd842aa617f09725a1f5429ebc822da238563f142b14993cccb85312d1874c`.

## Source argument and boundary ownership

The dispatch gate requires characteristic 2, exact sparse option 2, one
thread, no tracer, no normal form mode, no final-reduction mode, no elimination
variables, and a requested basis export. Other modes retain the old kernel.
The new routine checks these restrictions again and requires the known pivot
block to be columns 0 through ncl-1. Coefficients must all be exactly 1.

Each work row is reduced in increasing column order. A reducer's first
nonzero column is its pivot, so XOR does not introduce an earlier column.
The resulting nonzero rows therefore supply independent new pivots spanning
the same quotient row space modulo the old pivots. Descending-pivot
interreduction removes all other new pivot columns. This is ordinary exact
Gaussian elimination over F2.

The first draft assumed the entire sparse support was sorted. An owner
integrated fixture caught that the upstream converter preserves the leading
column first but may permute the tail. That draft failed closed and produced
no accepted basis. The corrected frozen version checks the leading column,
uniqueness, valid columns, and unit coefficients, while allowing arbitrary
tail order. The independent cases below include 961 unsorted-tail matrices.

Borrowed coefficient arrays remain basis-owned and are neither modified nor
freed. Lower sparse rows are released after copying into the work bitset.
Old reducer sparse rows are all freed before new sparse rows/coefficient
arrays are materialized. The lower pointer container is replaced only after
forward elimination. New rows retain their originating lower-row BINDEX and
MULT metadata, and COEFFS is the original lower-row position, matching the
generic serial convention. The matrix-to-basis converter consumes the
resulting standard sparse rows and coefficient arrays; clear_matrix frees
their pointer containers after that ownership transfer. DEG is set by the
existing converter, as before.

All checked allocation failures terminate with a nonzero error rather than
returning a partial basis. Sparse supports and ring variables remain distinct
concepts: packing matrix coefficients into bits adds no Boolean polynomial
identities. The ordinary x_i^3+1 domain equations remain unchanged.

## Independent checks

`exact_msolve_f2_matrix_review.py` compiles a harness that directly includes
the frozen actual kernel source. Its reference uses Python sets and separate
Gauss-Jordan elimination, rather than translating the bitset implementation.
It verifies exact reduced supports and original lower-row metadata, including
reversed borrowed coefficient slots.

Results in `exact_msolve_f2_matrix_review_results.json`:

- 1,039 matrices, 11,594 new pivots, 57 zero-output cases.
- Empty cases, full rank, dependencies, repeated rows, arbitrary tails,
  dense/sparse supports, and 63/64/65, 127/128/129 and larger word boundaries.
- Old reducer freeing before materialization and unchanged borrowed arrays
  checked by the harness.
- All 19 allocation sites on a nontrivial path fail closed when injected.
- Sixteen invalid input/mode cases fail closed.
- AddressSanitizer and UndefinedBehaviorSanitizer report no findings.

`exact_msolve_f2_basis_review.py` compares 12 distinct completed F2 ideals
against a separate Python Buchberger implementation and the prior executable.
All 24 full-basis exports match the Python reference, and candidate/prior
exports are byte-identical. The candidate actually enters the bitset routine
for 33 matrix rounds. Fixtures include coupled cubic roots, dense equations,
Frobenius partners, an inconsistent ideal, and a nonradical ideal. In
particular three independent cubics have dimension 27, the quadratic
coefficient-field fixture has dimension 2, and (x1^3,x2^2) has dimension 6.
These checks would fail under an accidental Boolean-variable reduction or
lost quotient multiplicity.

The initial basis invocation used a 1 GiB address-space limit and the prior
baseline crashed before producing a basis. A targeted comparison reproduced
this with 1 GiB and succeeded with the previously established 2 GiB limit.
All recorded complete comparisons use 2 GiB. The initial failure and its
diagnostic artifacts remain in `exact_msolve_f2_basis_review_runs`; they were
not counted as a passing basis. This is an observed baseline resource-limit
failure, not evidence of a candidate regression.

The owner separately reports 18 complete g1/g2 comparisons, including a saved
six-completion fiber, and four fallback mode comparisons. Those are owner
tests in `exact_msolve_f2_bitset_tools/validation.json` and
`mode_validation.json`, not additional independent runs claimed here.

The reviewed corrected executable hash has been added to the explicit
allowlist in `exact_msolve_cap_split.py`. No initial failed-draft hash is
accepted. Full count aggregation still requires all ten completed cap cases
and the strict per-result artifact audit.
