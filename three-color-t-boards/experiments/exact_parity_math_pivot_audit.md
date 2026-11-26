# Independent variable-order audit

**PASS.** The `--pivot-order` option simply renames the free board variables
bijectively. In both characteristics 2 and 29, reversing the renaming turns
every generated polynomial back into the natural-order model and matches an
independent reconstruction from centered Cartesian T placements.

For both full models, the prepared input has 100 ordinary cubic domains
`x_i³−1` and all 80 Fourier moments, with no prefix, normalization, coefficient
extension, or count multiplier or divisor. The first four variables now map to
original cells `0, 81, 90, 99`. Modular Gaussian elimination on the four unary
equations confirms these are the four pivot cells in both characteristics,
whereas natural order pivots on `0, 1, 2, 3`. Natural order puts all four pivots
in one T placement; dispersed pivots put at most one pivot in any T.

Mapping each new variable back to its original cell is a ring isomorphism that
preserves the cubic domains, all moment equations, and the quotient dimension.
It only changes which physical cells come first in grevlex order; this audit
makes no claim about solver speed.

The audit also checks prefix `0012` in both characteristics. Its 96 free board
variables are permuted, while the quadratic coefficient variable stays last as
variable 97. All coefficient arithmetic and all 80 moments match after inverse
renaming. The existing coefficient-extension divisor of 2 stays unchanged, with
no extra divisor from the permutation.

Preparation-only full-input SHA256 hashes:

* Characteristic 2: `a219416c206e31a2547155c62d5df1f3ef4050a303f5a90dde0d460c01e9768f`
* Characteristic 29: `699e6a81b2f4c1b113a448dc17e5b81f5962a365729204ae32802c857fd9944d`

Reproduce with `python experiments/exact_parity_math_pivot_audit.py`. The
checker saves the generated `.ms` inputs and metadata under
`exact_parity_math_pivot_*`, along with
[exact_parity_math_pivot_audit.json](exact_parity_math_pivot_audit.json).
**No solver was run and no full count was computed.**
