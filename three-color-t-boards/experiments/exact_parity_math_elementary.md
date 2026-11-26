# Elementary-symmetric consequences in characteristic two

Four extra quadratic generators capture information missing from the linear span
of the existing degree-two Fourier equations. Because they already lie in the
full exact ideal, adding them does not change the unrestricted count. No basis
or counting run is performed here.

## Exact multiplicity statement

Encode the three colors as the nonzero elements `1, ω, ω²` of `F₄`, where
`ω²+ω+1=0`. Each role `T, L, M, R` covers 81 **distinct** cells. On a valid
board, each color appears 27 times in every role, so the elementary-symmetric
generating polynomial of a role is

```
E(t) = ∏cells (1+z_cell t)
     = ((1+t)(1+ωt)(1+ω²t))^27
     = (1+t³)^27.
```

Hence `e1=e2=e4=e8=e16=0` for every role. These equations use ordinary powers
of `z`, with no Boolean relation `z²=z`.

For any nonnegative count triple `(n0, n1, n2)` summing to 81, adding these
conditions one by one refines the allowed triples as follows:

| Conditions | Each count is congruent to | Remaining count triples |
|---|---|---:|
| `e1=0` | `1 mod 2` | 820 |
| `e1=e2=0` | `3 mod 4` | 190 |
| additionally `e4=0` | `3 mod 8` | 55 |
| additionally `e8=0` | `11 mod 16` | 10 |
| additionally `e16=0` | `27 mod 32` | 1 |

**Proof.** Suppose the earlier conditions force each count to satisfy
`n_c ≡ a (mod 2^k)`, where `a = 27 mod 2^k` in `[0, 2^k)`. Write
`n_c = a + 2^k m_c` with each `m_c >= 0`. By Frobenius,

```
E(t) = (1+t³)^a ∏c (1+ζ_c^(2^k) t^(2^k))^m_c.
```

At `t^(2^k)`, the first factor has coefficient 0 and the second has no smaller
positive-degree terms, so the coefficient is `Σc (m_c mod 2) ζ_c^(2^k)`. The
only nontrivial binary linear dependence among the three nonzero elements of `F₄`
is that their sum is zero. So this coefficient vanishes if and only if all three
next bits `m_c mod 2` are equal. Their sum has parity `(81−3a)/2^k`, which is
the `k`th bit of 27, giving both directions of the induction step starting from
`k=0, a=0`. Finally, any nonnegative count congruent to 27 modulo 32 is at least
27, so summing to 81 forces all three counts to equal 27.

The generator independently checks both directions of each equivalence across
all `binomial(83,2)=3403` triples by multiplying the 81 linear factors over `F₄`
up to degree 16. Only `e2` and its Frobenius partners are exported here; the
much larger `e4, e8, e16` polynomials are not expanded.

## Sparse equivalent four-equation basis

For cell sets `A` and `B`, write `C=A∩B`, `D=A\B`, and `E=B\A`. Expanding
elementary symmetric polynomials over disjoint unions gives the exact `F₂`
identity

```
e2(A)+e2(B)+e2(D)+e2(E) = e1(C) (e1(A)+e1(B)).
```

Under the existing unary equations `e1(A)=e1(B)=0`, the right-hand side is
zero. The four raw role constraints are therefore equivalent to this sparser
basis:

```
e2(T),
e2(T\M)+e2(M\T),
e2(M\L)+e2(L\M),
e2(M\R)+e2(R\M).
```

These difference edges form a spanning tree on the four roles and minimize the
total term count among three-edge bases in the original ring: edges incident to
`T` cost 272 terms, `L-M` and `M-R` cost 72 terms each, `L-R` costs 272 terms,
and any spanning tree needs at least one edge touching `T`.

| Equation | Original terms | Reduced terms | Reduced square terms |
|---|---:|---:|---:|
| `e2(T)` | 3240 | 3240 | 80 |
| `T-M` difference | 272 | 2320 | 32 |
| `M-L` difference | 72 | 144 | 8 |
| `M-R` difference | 72 | 144 | 8 |

The reduced ring keeps the existing dispersed pivot substitutions for cells
`0, 81, 90, 99` and the same 96-variable order. Fresh Cartesian geometry and
Gaussian elimination reproduce the saved substitutions exactly, and both the
difference identity and its substituted form are verified symbolically.

The existing reduced source has six generators of ordinary degree at most 2,
with `F₂` coefficient-matrix rank 6. Adding these four quadratics raises the
rank to **10**. That proves they lie outside that low-degree linear span, though
it does not claim they are independent of higher-degree combinations from the
full ideal.

## Frobenius partners and preservation of the quotient

Each export holds eight generators: the four quadratics followed by their four
squares reduced modulo the ordinary cubic domains. Doubling exponents modulo 3
swaps `z_i` and `z_i²`, so the reduced partners have `80, 32, 8, 8` **linear**
terms alongside `3160, 2288, 136, 136` quartic terms. All linear terms are kept.
These partners follow from the quadratics and cubic domains and are separate
from the `e4=0` constraints.

The full Fourier ideal together with the cubic domains is radical. Over `F₄`,
the domain quotient splits into a product of copies of `F₄`, one per assignment
in `(F₄×)^100`, because each cubic has three distinct roots. Adding equations
removes some factors and leaves a product of fields. The full Fourier equations
keep exactly the valid boards. Since every exported elementary polynomial
vanishes on all valid boards, it already belongs to the ideal over `F₄`, and
hence to the `F₂` ideal by scalar-extension injectivity. Adding these generators
leaves the ideal and its quotient dimension unchanged.

Linear elimination is an isomorphism as long as all 96 free cubic domains and
all four substituted pivot-domain equations are kept, so the same argument holds
for the reduced exports. These files add redundant equations to the domain and
Fourier generators rather than replacing them. They target the full labeled
count with no fixed prefix, normalization, or multiplier.

## Artifacts and checks

- [Generator and checker](exact_parity_math_elementary.py).
- [Original 100-variable augmentation](exact_parity_math_elementary_original.json).
- [Reduced 96-variable augmentation](exact_parity_math_elementary_reduced.json).
- [Audit](exact_parity_math_elementary_audit.json).
- [Independent audit](exact_elementary_review_results.json), produced by
  [a separate checker](exact_elementary_review.py), verifies the frozen exports,
  ordinary-square expansions, and all 3403 histograms via Lucas-binomial
  coefficient enumeration.

The JSON monomial format matches the reduced Fourier export: two bits per
exponent, with coefficient 1 in `F₂`. `generator_groups` splits the four
quadratics from their four partners. Beyond the exhaustive count check and
symbolic identities, the audit checks 161 valid boards and 100 substitutions
over all of `F₄` (including zero values), and independently substitutes the
squared original equations to match the reduced partners.

```sh
python experiments/exact_parity_math_elementary.py
python experiments/exact_parity_math_elementary.py --check
```

The unrestricted quotient dimension is still uncomputed. Explicit low-degree
consequences may help a basis solver, though no speedup is claimed without a
completed comparison.
