# Four sparse quartic histogram consequences in prefix coordinates

The four role constraints `e4=0` can be added to the existing 96-variable
Gray-ordered prefix model using **14,194 ordinary quartic terms and no new
variables**. The sparse role-difference forms depend on the already kept unary
equations, the four `e2` equations, and the original-cell cubic domains. Adding
them leaves the unrestricted ideal and count unchanged. No solver was run here.

The frozen export is
[`exact_pivot_math_prefix_e4_constraints.json`](exact_pivot_math_prefix_e4_constraints.json),
SHA256 `dadaa5f4caf17b00311abe9000cf5463e101946bfc0ab9b2fb319f26838e8a91`, tied
to the prefix-coordinate certificate SHA256
`7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092`. It holds
four generators and **no Frobenius partners**:

| Label | Polynomial in original cell variables | Terms after prefix substitution |
|---|---|---:|
| `e4:T` | `e4(T)` | 12324 |
| `e4:T:M` | `e4(T\M)+e4(M\T)` | 1146 |
| `e4:M:L` | `e4(M\L)+e4(L\M)` | 278 |
| `e4:M:R` | `e4(M\R)+e4(R\M)` | 446 |

Every term has ordinary degree 4 and none is a pure fourth power, so the field
relations `y_i⁴=y_i` alone do not shorten these polynomials. The export keeps
the same 96 free-prefix variable order and 4-bit exponent packing as its source
model, with no prefix restriction, normalization, or count multiplier.

## Why the boundary differences are exact

Let `A` and `B` be two 81-cell role sets, and put `C = A∩B`, `D = A\B`, and
`E = B\A`. The unary equations force `e1(D) = e1(E) = e1(C) = s`. Expanding
elementary symmetric polynomials over disjoint unions gives

```
e4(A)+e4(B)+e4(D)+e4(E)
  = s*(e3(D)+e3(E)) + e2(C)*(e2(D)+e2(E)).
```

In characteristic 2, Newton's degree-three identity says
`e3(X) = p3(X) + e1(X)³ + e1(X)e2(X)`, where `p3 = Σ z³`. Because `D` and `E`
have equal size, the constants cancel and their combined cubic power sum equals
`Σ_(v∈D∪E)(z_v³+1)`. Under the unary equations, we also have
`e2(D) + e2(E) = e2(A) + e2(B)`. Substituting both gives the identity

```
e4(A)+e4(B)+e4(D)+e4(E)
 = (s²+e2(C))*(e2(A)+e2(B))
   + s*Σ_(v∈D∪E)(z_v³+1).
```

The checker verifies this as an **ordinary polynomial identity** after applying
the prefix-coordinate substitutions. So modulo the kept `e2` and cell-domain
equations, the three boundary equations match the three role differences.
Combined with `e4(T)`, they force `e4=0` on all four roles because the
difference edges form a spanning tree.

On any valid board, every role has 27 cells of each nonzero `F₄` color, so its
generating polynomial is `(1+t³)^27` and `e4=0`. As shown in
[the earlier multiplicity proof](exact_parity_math_elementary.md), adding
`e4=0` to `e1=e2=0` refines every color count from `3 mod 4` to `3 mod 8`.
Because the full Fourier and domain ideal is radical and already cuts out
exactly the valid boards, these quartics already lie in the ideal and leave its
quotient dimension unchanged.

## Why the top quartic has only 12,324 terms

The first 81 cells in the prefix order are the top-role cells. In 1-based
indexing, their colors are `z_i = p_i + p_(i−1)` with `p_0 = p_81 = 0`. All 80
interior prefixes stay distinct variables after the four unary eliminations
(one is simply renamed to a free prefix outside this segment).

Define the 159 quadratic monomials

```
S_i=p_i²            (1≤i≤80),
P_i=p_i*p_(i+1)     (1≤i≤79).
```

Sum the products of all distinct pairs of these 159 monomials, then drop the
three products `S_i*S_(i+1)`, `S_i*P_i`, and `S_(i+1)*P_i` for each adjacent
index `i`. That gives `e4(z_1, ..., z_81)` exactly as an ordinary polynomial,
with term count

```
binomial(159,2) − 3*79 = 12324.
```

To see why this path formula holds, classify the surviving monomials. Each
interior prefix appears in two adjacent linear factors, so no exponent can
exceed 2. Two squared prefixes survive if and only if they are nonadjacent.
For exponent shape `(2, 1, 1)`, the two singletons either sit next to each
other or flank the squared prefix. Four distinct prefixes survive if and only
if every consecutive run has even length. Those are exactly the products left
after dropping the adjacent triples above. The script also checks this formula
symbolically against direct elementary-coefficient recursion on the 81
substituted colors.

## Optional cubic lift: an explicit tradeoff, not the chosen export

For completeness, put `w_i = e2(z_1, ..., z_i)`. Then `w_0 = w_1 = 0` and

```
w_i+w_(i−1)+z_i*p_(i−1)=0.
```

Using `z_i³=1`, Newton's identity, and the existing condition `w_81=0` yields

```
e4 = Σ_(even i) z_i
   + Σ_(i=2..80) w_i*z_i²
   + Σ_(i=3..80) w_i*w_(i−1)
   + Σ_(i=2..80) w_i².
```

With 79 uniquely determined auxiliary variables, this would give 79 quadratic
definitions (315 terms) plus one cubic relation (395 terms), with no new
color-domain equations on the auxiliaries. That is an exact graph-variable
extension of the quotient, at the cost of 79 extra variables. It is **not
implemented or exported**, and we make no claim that it is faster. The carry
identity was checked across all 9840 nonzero-`F₄` sequences of lengths 1 to 8,
including all 2376 with final `e2=0`.

## Reproduction and scope

Run [the checker](exact_pivot_math_prefix_e4.py) with `--check` to verify the
frozen export and [audit](exact_pivot_math_prefix_e4.json):

```sh
python experiments/exact_pivot_math_prefix_e4.py --check
```

It rebuilds every original color form from the prefix order and four linear
eliminations, verifies the existing `e2` polynomials, expands every `e4` from
its generating product, checks all three ideal-membership identities, and
checks the top-path formula. The unrestricted count remains uncomputed. A
separate [independent review](exact_pivot_review_e4_results.json) reproduces
all four polynomials via a balanced generating-product tree, checks the three
correction identities and six Newton identities, and verifies the frozen export
hash.
