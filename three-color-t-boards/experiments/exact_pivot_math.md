# Alternative original-cell pivots: exact models and symbolic sizes

The proposed pivots `[6, 81, 90, 99]` work as expected: their linear
substitutions have `80, 17, 33, 17` terms, and the `T-M` elementary quadratic
shrinks from 2320 to **544** terms. A second pivot pattern cuts the overall
term count even further. These are symbolic size comparisons only; no solver or
counting run was performed here.

Cells are indexed by `row²+column`. Every chosen tuple has an invertible unary
coefficient matrix and puts at most one pivot in any T placement.

| Pivots | Substitution lengths | Pivot cubic terms | 40-moment model | 80-moment model | 80 moments + eight elementary generators |
|---|---|---:|---:|---:|---:|
| `[0,81,90,99]` (existing) | 80,17,80,17 | 13186 | 25070 | 36954 | 48650 |
| `[6,81,90,99]` | 80,17,33,17 | 7921 | 22267 | 36613 | 44757 |
| `[6,9,15,90]` | 54,17,17,31 | 4337 | 16659 | 28981 | 34409 |
| `[20,4,15,86]` | 54,17,17,31 | 4337 | 16625 | 28913 | 34341 |

All term counts leave out the 96 unchanged free cubics (another 192 terms). The
40-moment and 80-moment names refer to the original Fourier systems: four or
eight unary moments drop out after elimination, leaving 36 or 72 moments plus
the four kept pivot-domain equations. That makes 136 or 172 generators, or 144
and 180 once the eight elementary generators are added.

For the first family, we checked every upper cell while keeping the other three
pivots at `81, 90, 99`. Exactly 76 choices have at most one pivot per T, with
upper cell 56 giving the smallest 80-moment count in that family (36517 terms).
The last row in the table is the smallest among **60 explicitly tested
placements** of the second role-membership pattern; it is not claimed to be a
global optimum for moment size or solver speed. Full candidate lists are in the
audit file.

## A sharp but limited pivot-cubic support bound

Each eliminated cell comes from one nonzero binary combination of the four
unary role sums. If that combination covers `w` cells, removing the pivot
leaves `n = w−1` free variables. The four combinations must be linearly
independent. For `L = Σ_i z_i` over `n` distinct free cells, reducing modulo
the free cubics gives

```
L³+1 = Σ_(i≠j) z_i z_j² + (1 + n mod 2)
```

which has `n(n−1)+1` terms for even `n` and `n(n−1)` terms for odd `n`.

The 15 nonzero unary combinations have fixed cell-support sizes. Checking all
840 unordered independent 4-element bases proves that the minimum total support
across the four direct pivot cubics is **4337**. The unique minimizing set of
combinations is

```
L+M,  T+L+R,  M+R,  T+L+M+R,
```

with support sizes `18, 55, 18, 32` and substitution lengths `17, 54, 17, 31`.
Both of the last two pivot tuples achieve this lower bound with at most one
pivot per T.

This bound applies strictly to eliminating **four original cell variables** via
the four unary equations, expanding each pivot cubic directly, and reducing
only by the free cubics. It does not bound general linear coordinate changes,
other combinations of cubic generators, deeper ideal reductions, matrix sizes,
or solver runtime. In particular, the separate prefix-sum coordinates lie
outside this class and produce much smaller domain equations.

## Exact ideal and elementary augmentation

The four unary equations solve uniquely for the chosen original cells as linear
forms in the remaining 96, giving a ring isomorphism after quotienting by those
linear equations. Keeping all 96 free cubics and all four substituted pivot
cubics preserves the exact original color domains. Moment substitution follows
directly from the Cartesian placements, and having at most one pivot per T
keeps the expansion simple.

All 80 original nonconstant moments are generated from scratch. Eight unary
moments cancel to zero, and the remaining 72 pair up under Frobenius; the
40-moment version keeps one from each pair. Every reduction uses the ordinary
cubic relations, never Boolean idempotence.

The elementary equations are the same four proved consequences from
[the elementary-symmetric report](exact_parity_math_elementary.md):

```
e2(T), e2(T)+e2(M), e2(M)+e2(L), e2(M)+e2(R),
```

written with the sparse role-difference formulas before substitution. After
substitution, their term counts are:

- Pivot `p6`: `3240, 544, 144, 144` terms.
- Pivots `sparse` and `best`: `1772, 654, 144, 144` terms.

Each comes with its square reduced modulo the free cubics, keeping the linear
terms produced by `z_i⁴ = z_i`. All eight generators are redundant in the exact
Fourier ideal and leave the quotient dimension and counting scope unchanged.
Every export has no fixed prefix, no symmetry normalization, and count
multiplier and divisor 1.

## Reproducible exports

[The generator](exact_pivot_math.py) writes three named variants:

- `exact_pivot_math_p6_*`: pivots `[6, 81, 90, 99]`.
- `exact_pivot_math_sparse_*`: pivots `[6, 9, 15, 90]`.
- `exact_pivot_math_best_*`: pivots `[20, 4, 15, 86]`.

For each variant, `fourier40.json`, `fourier80.json`, and `elementary.json`
store the full free-variable map, original-cell substitution lists, and packed
polynomials. The matching `.ms` files are ordinary polynomial-ring inputs, and
`_e2.ms` appends the eight elementary generators. None of them was run in a
solver.

[The audit](exact_pivot_math_audit.json) logs every output SHA256, all search
metrics, and the finite support-bound certificate. It also verifies exact
reproduction of the frozen baseline, checks all 161 existing valid boards, and
tests 12 arbitrary substituted assignments per variant (comparing every kept
moment and pivot cubic against fresh geometry, and comparing the elementary
polynomials directly against their definitions). A separate
[independent audit](exact_pivot_review_original_results.json) also matches all
nine JSON models and twelve `.ms` inputs, including every ordinary domain
equation, using independently rebuilt geometry and tuple-polynomial arithmetic.

```sh
python experiments/exact_pivot_math.py
python experiments/exact_pivot_math.py --check
```

The unrestricted count is still uncomputed; smaller symbolic inputs do not
guarantee a smaller or faster Gröbner basis computation.
