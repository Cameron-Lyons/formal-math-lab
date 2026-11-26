# Independent elementary-symmetric augmentation audit

The mathematics and all eight frozen generator exports pass independent review. These polynomials are redundant generators of the full Fourier and domain ideal: they do not replace that ideal, compute a board count, or add a symmetry factor. No solver was run here.

Audited source hashes:

- `exact_parity_math_elementary_original.json`:
  `b24731564028877b8dd39850334b80810b776e271a064b89b46fd6b25f59782f`
- `exact_parity_math_elementary_reduced.json`:
  `4f8f351f5d11c27afc0b80b36c180e6f12fa7a90632eea2a709a0dae77a54d61`

## Histogram implications

Write the nonzero cube roots of unity in `F4` as `1, a, a²` with `a² + a + 1 = 0`. For color counts `(n0, n1, n2)`, the elementary symmetric generating polynomial is

```
E(t) = (1+t)^n0 (1+a*t)^n1 (1+a²*t)^n2.
```

When all three counts equal 27, `E(t) = (1 + t³)^27`, so every coefficient whose degree is not a multiple of 3 vanishes, including degrees 1, 2, 4, 8, and 16.

Conversely, take any nonnegative triple summing to 81. Vanishing coefficients at degrees 1, 2, 4, 8, and 16 force the counts to equal 27 modulo 2, 4, 8, 16, and 32 in turn. By induction, if all three counts equal `r (mod q)` where `q = 2^j`, write `n_i = r + q*m_i`. Frobenius gives

```
E(t) = (1+t³)^r * product_i (1+z_i^q*t^q)^mi.
```

Because 3 does not divide `q` and the second product has no positive degree below `q`, the `t^q` coefficient is `sum (m_i mod 2) * z_i^q`. Since `z_i^q` permutes `1, a, a²`, whose only `F2`-linear relation is their sum, this coefficient vanishes if and only if all three next bits `m_i mod 2` match, and summing to 81 fixes that shared bit. The forced residues are 1, 3, 3, 11, and 27 at moduli 2, 4, 8, 16, and 32; at modulus 32, every nonnegative count is at least 27, so summing to 81 forces `(27, 27, 27)`.

In particular, `e1 = e2 = 0` forces every count to be `3 (mod 4)`. Exporting the four `e2` equations and their Frobenius partners does not enforce `e4`, `e8`, or `e16` by itself; the full Fourier ideal remains in place.

An independent check using Lucas binomial parity and direct three-factor products verified all 3,403 nonnegative histograms summing to 81, leaving 820, 190, 55, 10, and 1 survivors after degrees 1, 2, 4, 8, and 16.

## Role differences and ordinary squares

For two role cell sets `A` and `B` with `C = A ∩ B`, splitting into shared and exclusive parts gives the ordinary polynomial identity

```
e2(A)+e2(B)+e2(A\B)+e2(B\A)
  = e1(C) * (e1(A)+e1(B)).
```

The sparse difference `e2(A\B) + e2(B\A)` therefore matches `e2(A) + e2(B)` only modulo the unary Fourier equations, not unconditionally; the audit checks the nonzero correction term explicitly on all three edges.

Using the spanning tree `T-M`, `M-L`, `M-R` together with `e2(T)` therefore imposes all four role `e2` equations modulo the unary equations. The four original term counts are 3,240, 272, 72, and 72. Fresh set-based Gaussian elimination on pivots 0, 81, 90, and 99 recovers the exact free-cell map and substitutions, and independent polynomial expansion matches every term of the four reduced exports (3,240, 2,320, 144, and 144 terms).

The reduced quadratics contain 80, 32, 8, and 8 ordinary square monomials, which must stay squared because `z² != z` in `F4`. Forming each Frobenius partner squares the polynomial and reduces modulo `z³ = 1` (swapping exponents 1 and 2), producing 80, 32, 8, and 8 linear terms and 3,160, 2,288, 136, and 136 quartic terms. All eight partners match independent expansion.

After linear elimination, adding the new quadratics raises the linear span of the six existing quadratic Fourier polynomials from rank 6 to rank 10. This measures low-degree linear span only; all new generators already lie in the full ideal.

## Why the quotient is unchanged

Let `R = F2[z1, ..., z100]`, let `D` be the ideal of all 100 cubics `z_i³ + 1`, and let `I` be the Fourier ideal plus `D`. Over `K = F4`, each cubic `z_i³ + 1` has derivative `z_i²` and therefore three distinct roots, so

```
K tensor_(F2) (R/D)  ≅  product over all root assignments of K.
```

Every ideal in this finite product of fields is radical and picks out a subset of coordinates. By the Fourier odd-count theorem, `I` selects exactly the valid labeled boards. Every valid board has role histograms `(27, 27, 27)`, so the new elementary polynomials vanish at every surviving coordinate and lie in the extended ideal. Since `R/I -> K tensor_(F2)(R/I)` is injective, they already belong to `I`. Adding them leaves the ideal, multiplicities, and quotient dimension completely unchanged.

Eliminating the four unary pivots gives an isomorphic quotient because all 96 free cubic domains and all 4 substituted pivot cubics stay in the reduced ideal, so the same argument applies after substitution. Frobenius partners are squares of existing generators reduced by kept domain cubics, so they are redundant too.

## Independent artifact checks

`exact_elementary_review.py` rebuilds all 81 placements from row indices, runs set-valued linear elimination with ordinary tuple monomials, decodes the packed exports strictly, and compares every term (`exact_elementary_review_results.json`). It checks 200 arbitrary `F4` assignments (including zeros), 200 nonzero free assignments for the Frobenius identity, and 24 valid boards. As expected from its balanced role histograms, the uniform-triple counterexample also satisfies every `e2` equation while having only 73 distinct T patterns, confirming that these equations cannot replace the Fourier constraints.

`exact_elementary_adapter_review.py` checks the actual backend definitions and fresh prepare-only outputs across ordinary row order, pivot order, `reduced40`, and `reduced80`. It rebuilds all eight appended equations independently and maps every monomial back through the inverse cell map. Every base polynomial (including all domains) matches byte for byte, giving variable/generator counts of 100/188, 100/188, 96/144, and 96/180, all with divisor 1 and unrestricted scope. Reduced partner linear terms are checked explicitly, and non-`F2`, prefix, binary, fixture, and conflicting reduced/pivot scopes are rejected. Neither script invokes a solver.

In adapter metadata, `source_sha256` hashes the emitted `.ms` file, `reduced_source_sha256` keeps the reduced JSON hash, and `base_input_sha256` keeps the unaugmented reduced input hash (distinct from `input_sha256`). An initial check mistakenly tested the old meaning of `source_sha256` after `run()`; we fixed that assertion while preserving its partial files. Verified fresh artifacts live under `exact_elementary_adapter_review_prepared_verified`, with hashes and `PREPARED_NOT_RUN` status in `exact_elementary_adapter_review_results.json`.
