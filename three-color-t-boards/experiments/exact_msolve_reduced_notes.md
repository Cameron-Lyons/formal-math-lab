# Reduced F2 msolve export

`exact_msolve_reduced.py` exposes `reduced_definitions(all_moments=False) -> (text, metadata)` without running a solver. It loads the independently reviewed reduced JSON, verifies its pinned SHA-256, and exports the 96-variable ordinary polynomial ring over F2.

Both modes include all 96 free cubic domains `x_i^3 + 1`, all 36 nonzero substituted representative moments, and all 4 substituted pivot-domain polynomials:

- **Default mode**: 136 generators and 25,070 terms outside the explicit free cubes. The four eliminated cells are 0, 81, 90, and 99, whose linear substitution map is bijective on valid boards.
- **All-moment mode**: appends the 36 Frobenius partners, giving 172 generators and 36,954 terms outside the free cubes. Partner generation swaps exponents 1 and 2 modulo the free cubes. Because `(A + B)^2 = A^2 + B^2` in characteristic 2, these partners are redundant members of the same ideal. The 4 pivot domains stay unchanged and unduplicated, and the default generator list appears as an exact prefix.

Validation rejects malformed inputs strictly:

- Term decoding rejects exponent 3, variable indices beyond 96, negative, non-hex, or non-string encodings, and duplicate monomials (including different textual spellings of the same integer).
- Document checks reject missing or duplicate equations, invalid free-cell maps, missing cube-domain metadata, inconsistent substitution data, and duplicate JSON keys.

Metadata records the full labeled ternary-board scope, no fixed prefix or symmetry normalization, divisor and multiplier equal to 1, exact source and emitted-input hashes, and the free original-cell map. `eliminated_unary_moments` is 4 in default mode (the 4 ordinary linear equations) or 8 in all-moment mode (adding their 4 quadratic unary partners).

Focused tests passed 25 invalid-input rejections, 243 small Frobenius monomial checks, and full polynomial round trips. A separate geometry audit by the math agent independently rebuilt all moments and all four pivot cubes and matched both `.ms` exports. Exporting these ideals does not compute a board count.

```sh
python experiments/exact_msolve_reduced_check.py
python experiments/exact_msolve_reduced.py experiments/exact_msolve_reduced_40.ms
python experiments/exact_msolve_reduced.py --all-moments experiments/exact_msolve_reduced_80.ms
```
