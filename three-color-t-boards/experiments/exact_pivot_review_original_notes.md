# Independent original-cell pivot audit

All three frozen pivot variants pass symbolic and emitted-input review. No
solver was run. The variant names come from the generator; calling the third
variant `best` is just a label and is not certified as a global optimum.

| Variant | Eliminated original cells | Substitution lengths | Four pivot-domain terms | 72 moment terms |
| --- | --- | --- | --- | ---: |
| p6 | 6,81,90,99 | 80,17,33,17 | 6321,272,1056,272 | 28692 |
| sparse | 6,9,15,90 | 54,17,17,31 | 2863,272,272,930 | 24644 |
| best | 20,4,15,86 | 54,17,17,31 | 2863,272,272,930 | 24576 |

`exact_pivot_review_original.py` starts from fresh row-index geometry and
set-based Gaussian elimination of the four unary role sums, deriving each pivot
substitution and ascending free-variable map independently. In all three
variants, every T placement contains at most one pivot. That keeps expansions
smaller, though correctness comes from linear elimination and the kept domain
equations rather than from that sparsity property.

Using ordinary tuple monomials, the verifier expands the four substituted
original cubic domains, all 80 Fourier moments, and all eight elementary
equations, reducing powers only modulo the kept free original-cell cubics.
Eight unary moments vanish, leaving 72. Ordinary squares stay squares, and
Frobenius partners are reduced using `z³=1` in this ring.

All nine JSON exports and all twelve `.ms` solver inputs match these
independent expansions across representative and all-moments modes, with and
without the `e2` augmentation. Every input keeps all 96 free cubic domains and
all four substituted pivot cubic domains. All 161 saved gauge witnesses
round-trip through each elimination map, and five are also evaluated on every
reconstructed constraint in each variant.

Because the unary equations already lie in the full Fourier and domain ideal,
the pivot matrix is invertible, and all original domain images are kept, each
quotient is isomorphic to the original full quotient. Every model keeps the
unrestricted labeled count as its quotient dimension, with divisor 1 and
multiplier 1. These preparation checks give no standard basis or numerical
count.

Exact file hashes and counts are saved in
`exact_pivot_review_original_results.json`.
