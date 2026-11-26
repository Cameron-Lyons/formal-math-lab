# Independent sparse e4 audit

All four frozen constraints and all four backend preparation modes pass
independent review. No solver was run by this audit. Source hash:
`dadaa5f4caf17b00311abe9000cf5463e101946bfc0ab9b2fb319f26838e8a91`.

`exact_pivot_review_e4.py` rebuilds the prefix coordinate map from fresh
row-index geometry and set-based Gaussian elimination. It expands elementary
symmetric coefficients with a balanced product tree in a formal parameter,
using ordinary tuple monomials, independent of the owner's sequential
recurrence and packed-nibble arithmetic. No variable exponent is reduced.

The exported polynomials are `e4(T)`, `e4(T\M)+e4(M\T)`, `e4(M\L)+e4(L\M)`, and
`e4(M\R)+e4(R\M)`, with `12,324`, `1,146`, `278`, and `446` terms. Every
monomial has ordinary degree 4. Every term matches the independent expansion,
and all five published boards satisfy all four equations.

## Required role-difference identity

For two equal-size roles `A` and `B`, put `C = A∩B`, `D = A\B`, `E = B\A`, and
`s = e1(C)`. The unary eliminations force `e1(D) = e1(E) = s`. Expanding
elementary symmetric functions on disjoint unions gives

```
e4(A)+e4(B)+e4(D)+e4(E)
  = e2(C)*(e2(D)+e2(E)) + s*(e3(D)+e3(E)).
```

In characteristic 2, Newton's degree-three identity is
`sum(z^3) = e1^3 + e1*e2 + e3`. Since `e1(D) = e1(E)`, the right-hand side
rewrites to

```
(s^2+e2(C))*(e2(A)+e2(B))
  + s*sum_(v in D union E)(z_v^3+1).
```

The constant terms in the last sum cancel because `|D| = |E|`. The audit checks
this as an exact ordinary-polynomial identity on all three role edges, along
with separate checks of all six Newton identities. The correction polynomials
have 9,062, 5,270, and 6,748 terms, so they cannot be dropped without the
underlying equations.

Once the role `e2` equations and all transformed original cubic domains are
kept, that correction vanishes in the quotient. Together with `e4(T)`, the
three sparse boundary equations therefore impose all four role `e4` conditions.
The backend requires prefix coordinates and the `e2` augmentation before
enabling `e4`, while the coordinate map itself enforces the unary equations.

The balanced-histogram proof already shows `e4=0` on every valid role. Going
the other way, adding `e4=0` to `e1=e2=0` forces each role color count to be
congruent to 3 modulo 8, as checked over all 3,403 histograms in the earlier
elementary audit. These equations are redundant consequences of the full
Fourier and domain ideal, not replacements for it. Because the full domain
quotient (and its isomorphic prefix-coordinate quotient) is radical, vanishing
on all valid boards implies ideal membership, so adding these generators leaves
the ideal and its quotient dimension unchanged.

## Top-path formula

For the 80 interior prefix forms `p_i` of the top role, define the quadratic
atoms `p_i^2` and `p_i*p_(i+1)`. The separately checked top formula equals the
second elementary symmetric function of those atoms plus

```
sum_i (p_i^2*p_(i+1)^2 + p_i^3*p_(i+1) + p_i*p_(i+1)^3).
```

Direct ordinary expansion matches `e4(T)` term for term, using no auxiliary
variables or extra domain relations.

## Actual backend inputs

`exact_pivot_review_e4_adapter.py` checks representative and all-moments modes,
each with the optional quartic field equations off and on. It checks every
appended monomial and the exact variable map, confirms that all prior input
bytes and all 100 transformed original cubic domains remain intact, and runs
fresh prepare-only exports with solver calls blocked.

The four modes have 148, 244, 184, and 280 generators, all with 96 variables,
divisor 1, multiplier 1, unrestricted scope, and exactly four added quartics.
Nine conflicting model and scope combinations are rejected. The prepared
all-moments + `e2` + field + `e4` input hash is
`72b09d3e2df822ea72f09dd1876580e950642a5681177d7aa604e8f6a68d9081`, built on
the previously audited base input hash
`60a5280098df62e0607fd3762a6e501b2d6098609b772138bd08f4f7ef867311`.

Outputs are in `exact_pivot_review_e4_results.json` and
`exact_pivot_review_e4_adapter_results.json`, with prepared files under
`exact_pivot_review_e4_prepared`. Every prepared record is marked
`PREPARED_NOT_RUN`, with no finished basis or count.
