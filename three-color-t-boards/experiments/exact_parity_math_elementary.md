# Elementary-symmetric consequences in characteristic two

Four additional quadratic generators expose information absent from the linear
span of the existing degree-two Fourier generators. They are redundant in the
full exact ideal, so adjoining them preserves the unrestricted count. No basis
computation or counting run is performed here.

## Exact multiplicity statement

Use the three nonzero elements `1,ω,ω²` of `F₄`, with `ω²+ω+1=0`. Each role
`T,L,M,R` occupies 81 **distinct** cells. On a valid board its three color
multiplicities are all 27. Its elementary-symmetric generating polynomial is

```
E(t) = ∏cells (1+z_cell t)
     = ((1+t)(1+ωt)(1+ω²t))^27
     = (1+t³)^27.
```

Consequently `e1=e2=e4=e8=e16=0` for every role. These constraints concern
ordinary powers of `z`; no Boolean relation `z²=z` is used.

In fact, for any nonnegative count triple `(n0,n1,n2)` summing to 81, the
successive vanishing conditions have this exact interpretation:

| Conditions | Each count is congruent to | Remaining count triples |
|---|---|---:|
| `e1=0` | `1 mod 2` | 820 |
| `e1=e2=0` | `3 mod 4` | 190 |
| additionally `e4=0` | `3 mod 8` | 55 |
| additionally `e8=0` | `11 mod 16` | 10 |
| additionally `e16=0` | `27 mod 32` | 1 |

**Proof.** Suppose the lower conditions have forced the common residue
`a=27 mod 2^k`, chosen in `[0,2^k)`. Write `n_c=a+2^k m_c`; all `m_c` are
nonnegative. Frobenius gives

```
E(t) = (1+t³)^a ∏c (1+ζ_c^(2^k) t^(2^k))^m_c.
```

The coefficient at `t^(2^k)` is
`Σc (m_c mod 2) ζ_c^(2^k)`: the first factor has zero coefficient there,
and the second has no positive terms of smaller degree. The sole nontrivial
binary dependence among the three nonzero elements of `F₄` is their sum zero.
Thus this coefficient vanishes exactly when the three next bits agree.
Their sum has parity `(81−3a)/2^k`, which equals the `k`th bit of 27. This
establishes the next common residue and the converse. Start at `k=0,a=0`.
Finally each nonnegative count congruent to 27 modulo 32 is at least 27;
their sum 81 forces all three to equal 27.

The generator independently checks both directions of each equivalence on all
`binomial(83,2)=3403` triples by multiplying the 81 linear factors over `F₄`,
truncated after degree 16. Only `e2` and its Frobenius partners are exported;
the much larger `e4,e8,e16` equations are not expanded here.

## Sparse equivalent four-equation basis

For cell sets `A,B`, let `C=A∩B`, `D=A\B`, `E=B\A`. Expanding elementary
symmetric polynomials in disjoint unions gives the exact `F₂` polynomial identity

```
e2(A)+e2(B)+e2(D)+e2(E) = e1(C) (e1(A)+e1(B)).
```

Under the existing unary equations `e1(A)=e1(B)=0`, the right side vanishes.
Therefore the four raw role constraints are equivalent to this basis:

```
e2(T),
e2(T\M)+e2(M\T),
e2(M\L)+e2(L\M),
e2(M\R)+e2(R\M).
```

The difference edges form a spanning tree on the four roles. They minimize
the total number of terms among such three-edge bases in the original ring:
the three edges incident to `T` cost 272 terms, `L–M` and `M–R` cost 72,
and `L–R` costs 272. At least one edge incident to `T` is required.

| Equation | Original terms | Reduced terms | Reduced square terms |
|---|---:|---:|---:|
| `e2(T)` | 3240 | 3240 | 80 |
| `T–M` difference | 272 | 2320 | 32 |
| `M–L` difference | 72 | 144 | 8 |
| `M–R` difference | 72 | 144 | 8 |

The reduced ring uses exactly the existing dispersed pivot substitutions for
cells `0,81,90,99`, leaving the established 96-variable order. Fresh Cartesian
geometry and Gaussian elimination reproduce the saved substitutions exactly.
The difference identity and its substituted version are checked symbolically.

The existing reduced source has exactly six generators of ordinary degree at
most two. Their `F₂` coefficient-matrix rank is six. Adding these four quadratic
polynomials raises that rank to **ten**. This proves they are new to that
low-degree linear span; it does not claim independence from the full ideal or
from consequences obtained through higher-degree multiplication/cancellation.

## Frobenius partners and preservation of the quotient

Each export contains eight generators: the four quadratics followed by their
four squares reduced modulo the ordinary cubic domains. Doubling exponents
modulo three sends `z_i` to `z_i²` and `z_i²` to `z_i`. Accordingly the reduced
partners have respectively `80,32,8,8` **linear** terms, together with
`3160,2288,136,136` quartic terms. None of those linear terms is discarded.
The partners are consequences of the quadratics and retained cubic domains;
they are not the separate constraints `e4=0`.

The full Fourier ideal with the cubic domains is radical. Over `F₄`, the domain
quotient is the product of one field for every assignment in `(F₄×)^100`, since
each cubic splits into three distinct roots. Adding equations keeps a product
of fields, possibly with some factors removed. The complete Fourier constraints
retain precisely the valid boards. Every exported elementary polynomial
vanishes on those boards, hence already belongs to the ideal over `F₄`, and
therefore also to its `F₂` ideal by scalar-extension injectivity. Adding the
generators changes neither the ideal nor its quotient dimension.

Linear elimination is an isomorphism after retaining **all** 96 free cubic
domains and all four substituted pivot-domain equations. The same argument
therefore applies to the reduced exports. These files are augmentations, not
replacements for either the domain or Fourier generators. Their scope is the
full labeled count, without a prefix, normalization, or multiplier.

## Artifacts and checks

- [Generator/checker](exact_parity_math_elementary.py).
- [Original 100-variable augmentation](exact_parity_math_elementary_original.json).
- [Reduced 96-variable augmentation](exact_parity_math_elementary_reduced.json).
- [Audit](exact_parity_math_elementary_audit.json).
- [Independent audit](exact_elementary_review_results.json), produced by
  [a separate checker](exact_elementary_review.py), confirms the frozen exports,
  ordinary-square expansion, and all 3403 histograms using Lucas-binomial
  coefficient enumeration.

The JSON monomial format matches the existing reduced Fourier export: two
bits per exponent, coefficients one in `F₂`. `generator_groups` identifies the
first four quadratics and the four partners. Besides the exhaustive count
check and symbolic identities, the audit checks 161 existing valid boards and
100 substitutions over all of `F₄`, including zero values. It independently
substitutes the squared original equations and matches their reduced partners.

```sh
python experiments/exact_parity_math_elementary.py
python experiments/exact_parity_math_elementary.py --check
```

The unrestricted quotient dimension remains unevaluated. These explicit
low-degree consequences may help a basis algorithm; no runtime benefit is
claimed without a completed comparison.
