# Reduced F2 msolve export

`exact_msolve_reduced.py` exposes
`reduced_definitions(all_moments=False) -> (text, metadata)` without invoking a
solver. It imports the independently reviewed reduced JSON, pins its exact
SHA256, and keeps the 96-variable ordinary polynomial ring over F2.

Both modes retain all 96 free cubic equations `x_i^3+1`, all 36 nonzero
substituted representative moments, and all four substituted pivot-domain
polynomials. Default mode has 136 generators and 25,070 terms outside the
explicit free cubes. The four eliminated cells are 0, 81, 90, and 99; their
linear substitution map is bijective on the constrained solutions.

All-moment mode appends exactly 36 Frobenius partners, yielding 172 generators
and 36,954 terms outside the free cubes. The partner transformation swaps
exponents one and two modulo the free cubic domains. In characteristic two
the square of a sum is the sum of its squares, so these partners are redundant
members of the same ordinary ideal. The pivot-domain polynomials are retained
unchanged and are not duplicated. All default polynomials remain an exact
prefix of the larger polynomial list.

The term decoder rejects exponent three, bits beyond the 96 variables,
negative/nonhex/nonstring encodings, and duplicate monomials including
different textual spellings of the same integer. Document checks reject
missing or duplicate equations, invalid free-cell maps, missing cube-domain
metadata, and inconsistent substitution data. JSON duplicate keys are also
rejected.

Metadata records full labeled ternary-board scope, no fixed prefix or
symmetry normalization, count divisor/multiplier one, exact source and
emitted-input hashes, and the free original-cell map. `eliminated_unary_moments`
is four or eight according to mode; only four are ordinary linear equations,
while all-moment mode additionally eliminates their quadratic unary partners.

Focused checks passed 25 invalid-input cases, 243 small Frobenius monomial
cases, and complete emitted-polynomial round trips. A separate fresh geometry
audit by the math agent independently reconstructed all moments and all four
pivot cubes and matched both actual `.ms` exports. No exact numerical count
is obtained by exporting these generating ideals.

```sh
python experiments/exact_msolve_reduced_check.py
python experiments/exact_msolve_reduced.py experiments/exact_msolve_reduced_40.ms
python experiments/exact_msolve_reduced.py --all-moments experiments/exact_msolve_reduced_80.ms
```
