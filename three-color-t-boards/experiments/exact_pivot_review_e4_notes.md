# Independent sparse e4 audit

The four frozen constraints and all four backend preparation variants pass
independent review. No solver was run by this audit. The source hash is
`dadaa5f4caf17b00311abe9000cf5463e101946bfc0ab9b2fb319f26838e8a91`.

`exact_pivot_review_e4.py` reconstructs the prefix coordinate map from fresh
row-index geometry and set-based Gaussian elimination. It computes elementary
coefficients by a balanced product tree in a formal parameter, using ordinary
tuple monomials. This is independent of the owner's sequential recurrence
and packed-nibble arithmetic. No variable exponent is reduced.

The exact exported polynomials are e4(T), e4(T\M)+e4(M\T),
e4(M\L)+e4(L\M), and e4(M\R)+e4(R\M), with respective term counts
12,324, 1,146, 278, and 446. Every monomial has ordinary degree four.
All terms match the independently expanded polynomials, and all five
published boards satisfy them.

## Required role-difference identity

For two roles A,B of equal size, set C=A∩B, D=A\B, E=B\A and s=e1(C).
The retained unary elimination makes e1(D)=e1(E)=s. Expanding elementary
functions on disjoint unions gives

```
e4(A)+e4(B)+e4(D)+e4(E)
  = e2(C)*(e2(D)+e2(E)) + s*(e3(D)+e3(E)).
```

In characteristic two, Newton's degree-three identity is
`sum(z^3)=e1^3+e1*e2+e3`. Since e1(D)=e1(E), this converts the preceding
expression into

```
(s^2+e2(C))*(e2(A)+e2(B))
  + s*sum_(v in D union E)(z_v^3+1).
```

The constants in the last sum cancel because |D|=|E|. The audit checks this
as an exact ordinary-polynomial identity for each of the three role edges,
including separate checks of the six Newton identities. The nonzero
correction polynomials have 9,062, 5,270, and 6,748 terms; they cannot be
dropped unconditionally.

With the existing role e2 equations and all transformed original cubic
domains retained, the correction vanishes in the quotient. Hence the three
sparse boundary equations, together with e4(T), impose exactly all four
role e4 conditions. The backend requires prefix coordinates and the e2
augmentation before allowing e4. The unary equations remain enforced by the
coordinate map.

The balanced-histogram proof already establishes e4=0 on every valid role.
Conversely, adding e4=0 to e1=e2=0 makes each role color count congruent to3
modulo8, as verified over all 3,403 histograms in the earlier elementary
audit. This is a redundant consequence of the full Fourier/domain ideal,
not a replacement for it. Radicality of that complete domain quotient, or
its isomorphic prefix-coordinate quotient, upgrades pointwise vanishing to
ideal membership. Adding these generators preserves the ideal and its
exact quotient dimension.

## Top-path formula

For the 80 interior prefix forms p_i of the top role, define quadratic atoms
`p_i^2` and `p_i*p_(i+1)`. The separately checked top formula is the second
elementary function of those atoms, plus

```
sum_i (p_i^2*p_(i+1)^2 + p_i^3*p_(i+1) + p_i*p_(i+1)^3).
```

Direct ordinary expansion agrees exactly with e4(T). No auxiliary variables
or additional domain assumptions are used.

## Actual backend inputs

`exact_pivot_review_e4_adapter.py` verifies representative/all moments with
the optional quartic field equations off/on. It compares every appended
monomial and the exact variable map, checks that all prior input bytes and
100 transformed original cubic domains remain, and exercises fresh
prepare-only outputs with solver calls explicitly forbidden.

Generator counts are 148,244,184,280, respectively, all with 96 variables,
divisor one, multiplier one, unrestricted scope and exactly four added
quartics. Nine conflicting model/scope combinations are rejected. The
prepared all-moments/e2/field/e4 input hash is
`72b09d3e2df822ea72f09dd1876580e950642a5681177d7aa604e8f6a68d9081`.
Its base input hash is the previously audited
`60a5280098df62e0607fd3762a6e501b2d6098609b772138bd08f4f7ef867311`.

Results are in `exact_pivot_review_e4_results.json` and
`exact_pivot_review_e4_adapter_results.json`; prepared files are under
`exact_pivot_review_e4_prepared`. Every prepared result is explicitly
`PREPARED_NOT_RUN`, with no completed basis or count.
