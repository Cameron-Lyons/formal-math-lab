# Alternative original-cell pivots: exact models and symbolic sizes

The proposed pivots `[6,81,90,99]` work: their linear substitutions have
`80,17,33,17` terms, and the `T–M` elementary quadratic shrinks from 2320
to **544** terms. A second pivot pattern gives a larger overall reduction.
These are symbolic comparisons; no solver or complete count was run.

Cells use index `row²+column`. Every selected tuple has an invertible unary
coefficient matrix and at most one pivot in each T placement.

| Pivots | Substitution lengths | Pivot cubic terms | 40-moment model | 80-moment model | 80 moments + eight elementary generators |
|---|---|---:|---:|---:|---:|
| `[0,81,90,99]` (existing) | 80,17,80,17 | 13186 | 25070 | 36954 | 48650 |
| `[6,81,90,99]` | 80,17,33,17 | 7921 | 22267 | 36613 | 44757 |
| `[6,9,15,90]` | 54,17,17,31 | 4337 | 16659 | 28981 | 34409 |
| `[20,4,15,86]` | 54,17,17,31 | 4337 | 16625 | 28913 | 34341 |

All term counts exclude the unchanged 96 free cubics, which contribute another
192 terms. The 40/80 names refer to the original Fourier systems: four/eight
unary moments vanish after elimination, leaving 36/72 moments and four retained
pivot-domain equations. Thus these models have 136/172 generators, or 144/180
after adjoining the eight elementary generators.

The initial family was checked for every upper cell with the other pivots fixed
at `81,90,99`. Exactly 76 choices have at most one pivot per T; the best in
that family is upper cell 56, with 36517 terms in the 80-moment model. The final
row in the table is the best of **60 explicitly tested placements** of the
second role-membership pattern. It is not a global optimum for moment support
or solver performance. The full candidate lists are in the audit.

## A sharp but limited pivot-cubic support bound

Each eliminated cell is expressed by one nonzero binary combination of the four
unary role sums. If that combination contains `w` cells, its expression after
removing the pivot has `n=w−1` free variables. The four combinations must be
linearly independent. For `L=Σ_i z_i` on `n` distinct free cells,

```
L³+1 = Σ_(i≠j) z_i z_j² + (1 + n mod 2)
```

modulo the retained free cubics. Its support therefore has
`n(n−1)+1` terms for even `n`, or `n(n−1)` for odd `n`.

The 15 nonzero unary combinations have fixed cell-support sizes. Exhausting
their 840 unordered independent four-element bases proves that the smallest
sum of these four direct cubic supports is **4337**. The unique minimizing
combination set is

```
L+M,  T+L+R,  M+R,  T+L+M+R,
```

with support sizes `18,55,18,32`, hence substitution sizes `17,54,17,31`.
Both of the last two pivot tuples realize this bound with no shared T.

The bound concerns elimination of **four original cell variables** with the
four unary equations, followed by direct expansion of each pivot cubic and
reduction only by free cubics. It does not bound arbitrary linear coordinate
changes, alternative combinations of the cubic generators, further ideal
reductions, matrix sizes, or runtime. In particular, the separately developed
prefix-sum coordinates are outside this class and can have much smaller domain
generators.

## Exact ideal and elementary augmentation

The four unary equations solve uniquely for the selected original cells as
linear forms in the remaining 96. Substitution induces an isomorphism after
quotienting by those linear equations. Retaining all 96 ordinary free cubics
and all four substituted pivot cubics preserves exactly the original color
domains. The moment substitution is direct from the Cartesian placement set;
the at-most-one-pivot property makes the expansion especially simple.

All 80 original nonconstant moments are generated afresh. Exactly eight unary
moments vanish, and the remaining 72 agree pairwise under Frobenius. The
40-moment version retains one from each conjugate pair. All calculations use
the ordinary cubic relations, never Boolean idempotence.

The elementary equations are the same four proven consequences from
[the elementary-symmetric report](exact_parity_math_elementary.md):

```
e2(T), e2(T)+e2(M), e2(M)+e2(L), e2(M)+e2(R),
```

represented by the sparse role-difference identities before substitution.
Their respective reduced supports are:

- Pivot `p6`: `3240,544,144,144` terms.
- Pivots `sparse` and `best`: `1772,654,144,144` terms.

Each is accompanied by its square reduced modulo the free cubics. Linear
terms created by `z_i⁴=z_i` remain present. The eight generators are redundant
in the exact Fourier ideal and change neither its quotient dimension nor the
counting scope. Every export has no fixed prefix, no symmetry normalization,
and count multiplier/divisor one.

## Reproducible exports

[The generator](exact_pivot_math.py) writes three named variants:

- `exact_pivot_math_p6_*`: pivots `[6,81,90,99]`.
- `exact_pivot_math_sparse_*`: pivots `[6,9,15,90]`.
- `exact_pivot_math_best_*`: pivots `[20,4,15,86]`.

For each, `fourier40.json`, `fourier80.json`, and `elementary.json` record the
complete free-variable map, original-cell substitution lists, and packed
polynomials. The corresponding `.ms` files contain ordinary polynomial-ring
inputs; `_e2.ms` appends the eight elementary generators. None is executed.

[The audit](exact_pivot_math_audit.json) lists every output SHA256, all search
metrics, and the finite support-bound certificate. It also records exact
reproduction of the frozen baseline, evaluation against 161 existing valid
boards, and 12 arbitrary substituted assignments for each exported variant.
The latter compare every retained moment and pivot cubic against fresh full
geometry, and compare elementary values directly against their definitions.
The separate [independent audit](exact_pivot_review_original_results.json)
also matches all nine JSON models and twelve emitted inputs, including every
ordinary domain equation, using independently reconstructed geometry and
tuple-polynomial arithmetic.

```sh
python experiments/exact_pivot_math.py
python experiments/exact_pivot_math.py --check
```

The unrestricted count remains unevaluated; smaller symbolic input does not
establish a smaller completed Gröbner-basis computation.
