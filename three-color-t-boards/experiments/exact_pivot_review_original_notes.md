# Independent original-cell pivot audit

All three frozen variants pass symbolic and actual-input review. No solver
was run. Their names identify the generator's candidates; this review does
not certify a global optimization claim for the variant named `best`.

| Variant | Eliminated original cells | Substitution lengths | Four pivot-domain terms | 72 moment terms |
| --- | --- | --- | --- | ---: |
| p6 | 6,81,90,99 | 80,17,33,17 | 6321,272,1056,272 | 28692 |
| sparse | 6,9,15,90 | 54,17,17,31 | 2863,272,272,930 | 24644 |
| best | 20,4,15,86 | 54,17,17,31 | 2863,272,272,930 | 24576 |

`exact_pivot_review_original.py` starts from fresh row-index geometry and
set-valued Gaussian elimination of the four unary role sums. It derives
each pivot substitution and the ascending original-cell free-variable map
independently. Every T contains at most one selected pivot in each variant.
The latter fact is useful for expansion size, but correctness follows from
linear elimination and retained domains, not from that sparsity condition.

The verifier expands the four substituted original cubic domains, all 80
Fourier moments, and the eight elementary equations with tuple monomials.
It reduces powers only modulo the explicitly retained free original-cell
cubics. Exactly eight unary moments vanish, leaving 72. Ordinary squares
remain squares; Frobenius partners are reduced with z³=1 in this ring.

All nine JSON exports and all twelve complete solver input files match these
independent expressions, including representative/all moments and each e2
augmentation. Every input retains all 96 free cubic domains and all four
substituted pivot cubic domains. All 161 saved gauge witnesses round-trip
through each elimination map; five are also evaluated on every reconstructed
constraint in each variant.

The quotient is isomorphic to the original full Fourier/domain quotient:
the unary equations already belong to it, the pivot coefficient matrix is
invertible, and the images of all original domains remain. Thus each model
still has the unrestricted labeled count as its quotient dimension, with
divisor one and multiplier one. These preparation audits provide no
completed standard basis or numerical count.

Exact file hashes and counts are retained in
`exact_pivot_review_original_results.json`.
