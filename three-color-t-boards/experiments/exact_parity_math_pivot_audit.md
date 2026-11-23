# Independent variable-order audit

**PASS.** The new `--pivot-order` option is a bijective renaming of free board
variables. At both characteristics 2 and 29, undoing that renaming makes every
generated polynomial identical to the natural-order model and to an independent
reconstruction from centered Cartesian T placements.

For each full model, the prepared input contains 100 ordinary cubic domains
`x_i³−1` and all 80 Fourier moments, with no prefix, normalization, coefficient
extension, or count multiplier/divisor. The first four variables now represent
original cells `0,81,90,99`. Modular Gaussian elimination of the four unary
equations confirms these are the four pivot cells in both characteristics;
natural order instead pivots on `0,1,2,3`. The natural set lies in one T,
whereas every T contains at most one dispersed pivot.

The ring isomorphism sends each new variable to its recorded original cell.
It preserves the cubic domains and all moment equations, hence preserves the
quotient dimension. It changes which physical cells occur first in grevlex
order; no assertion about its runtime benefit follows from this audit.

The audit also checks prefix `0012` at both characteristics. Its 96 free board
variables are permuted, while the quadratic coefficient variable remains
last, at variable 97. All coefficient arithmetic and all 80 moments agree
after inverse renaming. The existing coefficient-extension divisor two is
unchanged; no extra divisor is introduced by the permutation.

The actual preparation-only full inputs have SHA256 hashes:

* Characteristic 2: `a219416c206e31a2547155c62d5df1f3ef4050a303f5a90dde0d460c01e9768f`
* Characteristic 29: `699e6a81b2f4c1b113a448dc17e5b81f5962a365729204ae32802c857fd9944d`

Reproduce with
`python experiments/exact_parity_math_pivot_audit.py`.
The checker saves the generated `.ms` inputs and metadata under
`exact_parity_math_pivot_*`, plus
[exact_parity_math_pivot_audit.json](exact_parity_math_pivot_audit.json).
**No solver was invoked and no full count was evaluated.**
