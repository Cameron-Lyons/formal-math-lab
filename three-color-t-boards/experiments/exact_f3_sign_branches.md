# Four disjoint linear sign branches

The full labeled board count splits cleanly into four branch totals:

```
N = N0 + N1 + N2 + N3.
```

Each `Nk` is the quotient dimension of one exported `F₃` ideal. Because the independent three-valued shift and two-valued sign stay inside every ideal, **no extra multiplier or divisor applies**. None of the four unrestricted counts has been computed. Natural and minimum-fill exports are two variable orders of the same four branches, not eight separate summands.

## Disjoint partition and exact reconstruction

Using the same placement pair as the quintic selector,

```
P0 = (0,1,2,3),  P3 = (3,6,7,8),
Delta(z) = pattern(P0, z) - pattern(P3, z),  in T,L,M,R order,
```

every valid board has `Delta != 0`. Let `k` be the index of its first nonzero entry, and set

```
a = z_apex,  D = z - a,  s = Delta_k(D),  d = s*D.
```

Since `s ∈ {1, -1}`, `s² = 1`, and the canonical board `d` satisfies `d_apex = 0`, `Delta_i(d) = 0` for `i < k`, and `Delta_k(d) = 1`. Conversely, any such `d` with independent `a ∈ F₃` and `s ∈ {1, -1}` gives

```
z_cell = a + s*d_cell,
```

which recovers `k` as the first nonzero difference and `s` as the sign. The maps are mutual inverses, so the four branches partition all labeled valid boards without overlap.

Affine color permutations preserve validity; shift is already factored out in the frozen source, and negation preserves both the native moments (the only nonzero target sits at even degree 8) and the `e3` zero equations. The exporter checks directly that every coupled source polynomial keeps uniform degree parity after field reduction.

Every variable keeps its field cubic, so every quotient is a finite product of copies of `F₃` counting solutions without multiplicity:

```
A_k ≅ F₃[a]/(a³ - a) ⊗ F₃[s]/(s² - 1) ⊗ A_canonical,k.
```

We also include the redundant `s³ - s = s(s² - 1)` for uniform input structure.

## Four sparse linear systems

In natural prefix order, the four role differences are

```
Delta_T = 2*x1,
Delta_L = 2*x16 + 2*x71 + x72 + x94,
Delta_M = 2*x8 + 2*x9 + 2*x10,
Delta_R = 2*x1 + 2*x2.
```

Branch `k` sets the first `k` forms to 0 and form `k` to 1. Both coefficient and augmented ranks equal `k + 1`, so the linear system is consistent in the ambient prefix space (though consistency alone does not guarantee valid board completions).

| Branch | First nonzero role | Added linear constraints | Terms in those constraints | Total generators |
|---|---|---:|---:|---:|
| 0 | T | 1 | 2 | 179 |
| 1 | L | 2 | 6 | 180 |
| 2 | M | 3 | 9 | 181 |
| 3 | R | 4 | 11 | 182 |

Every input has 97 variables: 95 canonical prefix coordinates, offset `a` at 0-based index 95, and sign `s` at index 96. It appends `s³ - s`, `s² - 1`, and the `k + 1` linear constraints directly after the 176 frozen translated-plus-`e3` generators, with no quintic selector. Source polynomial bodies stay byte-for-byte identical in both variable orders.

Branch 0 fixes `x1 = 2` directly, and every branch introduces a nonzero constant at degree 1 (versus degree 5 for the quintic selector and degree 8 for `M_2222`). That may help early elimination, at the cost of solving four branches instead of one; no unrestricted solver performance has been measured here.

## Exports and counting rule

The [manifest](exact_f3_sign_branches_manifest.json) lists all four branch IDs, both variable orders with hashes, the sum rule, and the completion rule. The inputs are `exact_f3_sign_branch{k}_{natural,minfill}.ms` with companion JSON metadata storing source hashes, added polynomials, coordinate maps, bilinear original-color forms, and (for minimum-fill) both directions of the permutation.

Original-color fixes must use `a + s*d_cell = color`. On the known 81-cell six-completion prefix, `Delta = [1, 2, 0, 2]`, so `k = 0`, `a = 1`, `s = 1`, predicting branch counts `[6, 0, 0, 0]` (deduced from the known prefix count; this exporter runs no solver).

Only report an unrestricted total `N` once every branch has a certified complete count. Missing, partial, or timed-out branches stay unknown, never zero. Never sum both variable orders, and never multiply a branch count by 6, because both shift and sign are already inside each ideal.

## Symmetry scope and checks

Every color permutation over `F₃` has the form `z ↦ alpha*z + beta` (`alpha ∈ {1, -1}`), scaling `Delta` by `alpha` and preserving its first nonzero coordinate, so palette symmetry relates no two distinct branches.

Horizontal reflection maps `P3` to `P1` and swaps left and right roles. Explicit valid board pairs stored in the audit show that branch 0 reflects into both branches 0 and 1, and branch 1 reflects into both as well, so reflection does not swap branches uniformly. We claim no equality among `N0..N3`, no empty branch, and no broader symmetry obstruction.

Exhausting all 80 nonzero difference vectors splits them into sizes `54, 18, 6, 2` (and normalized sizes `27, 9, 3, 1`); those reflect vector space slices, **not board-count ratios**. The checker also validates 161 existing boards geometrically, round-trips all six affine palettes for each, and checks five complete polynomial fixtures. Those 161 stored witnesses land solely in branches 0 and 1 (12 and 149 respectively), which does not mean branches 2 or 3 are empty.

Run `python experiments/exact_f3_sign_branches.py --check` to regenerate the [audit](exact_f3_sign_branches_audit.json) and verify all eight inputs, verbatim source bodies, 97 field domains, linear ranks, inverse permutations, finite partition, and witnesses. No backend or earlier model changed, and no solver ran.
