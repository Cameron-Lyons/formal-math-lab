# Four sparse quartic histogram consequences in prefix coordinates

The four role constraints `e4=0` admit an exact augmentation with **14,194
ordinary quartic terms and no new variables** in the existing 96-variable
Gray-ordered prefix model. The role differences require the already retained
unary equations, four `e2` conditions, and original-cell cubic domains. They
preserve the unrestricted ideal and count. No solver is run here.

The frozen augmentation is
[`exact_pivot_math_prefix_e4_constraints.json`](exact_pivot_math_prefix_e4_constraints.json),
SHA256 `dadaa5f4caf17b00311abe9000cf5463e101946bfc0ab9b2fb319f26838e8a91`.
It is tied to the prefix-coordinate certificate SHA256
`7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092`.
It contains four generators, with **no Frobenius partners**:

| Label | Polynomial in original cell variables | Terms after prefix substitution |
|---|---|---:|
| `e4:T` | `e4(T)` | 12324 |
| `e4:T:M` | `e4(T\M)+e4(M\T)` | 1146 |
| `e4:M:L` | `e4(M\L)+e4(L\M)` | 278 |
| `e4:M:R` | `e4(M\R)+e4(R\M)` | 446 |

Each term has ordinary degree four. None is a pure fourth power, so the
relations `y_i⁴=y_i` alone do not shorten these polynomials. The export uses
the same 96 free-prefix-variable order and four-bit exponent encoding as its
source model. It adds no prefix restriction, normalization, or count multiplier.

## Why the boundary differences are exact

Let `A,B` be two 81-cell role sets and write `C=A∩B`, `D=A\B`, `E=B\A`.
The unary equations imply `e1(D)=e1(E)=e1(C)=s`. Disjoint-union expansion gives

```
e4(A)+e4(B)+e4(D)+e4(E)
  = s*(e3(D)+e3(E)) + e2(C)*(e2(D)+e2(E)).
```

Newton's degree-three identity in characteristic two is
`e3(X)=p3(X)+e1(X)³+e1(X)e2(X)`, where `p3=Σ z³`. Since the exclusive sets
have equal size, their combined cubic power sum equals
`Σ_(v∈D∪E)(z_v³+1)`. Also `e2(D)+e2(E)=e2(A)+e2(B)` under the unary
equations. Substitution proves the explicit identity

```
e4(A)+e4(B)+e4(D)+e4(E)
 = (s²+e2(C))*(e2(A)+e2(B))
   + s*Σ_(v∈D∪E)(z_v³+1).
```

The checker verifies this as an **ordinary polynomial identity** after the
actual prefix-coordinate substitutions. Therefore the boundary equations
are equivalent to the corresponding role differences modulo precisely the
retained `e2` and cell-domain equations. Together with `e4(T)` they force all
four role `e4` values to vanish, since the difference edges form a spanning
tree on the roles.

On every valid board, each role has exactly 27 occurrences of each nonzero
`F₄` color, so its generating polynomial is `(1+t³)^27` and `e4=0`.
[The earlier multiplicity proof](exact_parity_math_elementary.md) shows that,
with `e1=e2=0`, adding `e4=0` refines each color count from `3 mod 4` to
`3 mod 8`. Since the full Fourier/domain ideal is radical and already
characterizes valid boards, these quartics belong to that ideal. Adjoining
them does not change its quotient dimension.

## Why the top quartic has only 12,324 terms

The first 81 cells in the prefix order are the top-role cells. In one-based
notation their colors satisfy `z_i=p_i+p_(i−1)`, with `p_0=p_81=0`. The
interior 80 prefixes remain distinct variables after the other unary
substitutions; one is renamed to a free prefix outside this segment.

Form the 159 quadratic monomials

```
S_i=p_i²            (1≤i≤80),
P_i=p_i*p_(i+1)     (1≤i≤79).
```

Take the sum of products of every distinct pair of these monomials. Delete
the three products `S_i*S_(i+1)`, `S_i*P_i`, and `S_(i+1)*P_i` for each
adjacent index. The result is exactly `e4(z_1,…,z_81)` as an ordinary
polynomial, and its support size is

```
binomial(159,2) − 3*79 = 12324.
```

One way to verify the general path identity is to classify monomials. Each
interior prefix occurs in exactly two neighboring linear factors, so no
exponent exceeds two. Two squared prefixes survive precisely when they are
nonadjacent. For exponents `(2,1,1)`, the singleton pair is either adjacent,
or consists of the two neighbors of the squared prefix. Four distinct
prefixes survive precisely when their consecutive runs all have even length.
Those are exactly the remaining products above. The implementation also
compares this formula symbolically with direct elementary-coefficient
recursion on the actual 81 substituted colors.

## Optional cubic lift: an explicit tradeoff, not the chosen export

For completeness, define `w_i=e2(z_1,…,z_i)`. Then `w_0=w_1=0` and

```
w_i+w_(i−1)+z_i*p_(i−1)=0.
```

Using `z_i³=1`, Newton's identity, and the existing final condition `w_81=0`
gives

```
e4 = Σ_(even i) z_i
   + Σ_(i=2..80) w_i*z_i²
   + Σ_(i=3..80) w_i*w_(i−1)
   + Σ_(i=2..80) w_i².
```

Thus 79 uniquely determined auxiliary values would permit 79 quadratic
definitions with 315 terms and one cubic relation with 395 terms. No new
color-domain constraints belong on those auxiliary values. This is an exact
graph-variable extension of the quotient, but adds 79 variables; it is **not
implemented or exported**, and no speedup is asserted. The carry identity
is independently checked on all 9840 nonzero-`F₄` sequences of lengths one
through eight, including all 2376 with final `e2=0`.

## Reproduction and scope

Run [the checker](exact_pivot_math_prefix_e4.py) with `--check` to verify the
frozen augmentation and [audit](exact_pivot_math_prefix_e4.json):

```sh
python experiments/exact_pivot_math_prefix_e4.py --check
```

It reconstructs every original color form from the prefix order and four
linear eliminations, verifies the existing `e2` polynomials, derives every
`e4` from its generating product, checks the three ideal-membership identities,
and checks the top path formula. The complete count remains unevaluated.
The separate [independent review](exact_pivot_review_e4_results.json) reproduces
all four polynomials with a balanced generating-product tree, checks the
three correction identities and six Newton identities, and confirms the
frozen augmentation hash.
