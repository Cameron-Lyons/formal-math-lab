# Independent elementary-symmetric augmentation audit

The mathematics and the eight frozen generator exports pass independent
review. They are redundant generators for the existing full Fourier/domain
ideal. They do not replace that ideal, establish a board count, or supply a
new symmetry factor. No solver was run for this audit.

The audited source hashes are:

- `exact_parity_math_elementary_original.json`:
  `b24731564028877b8dd39850334b80810b776e271a064b89b46fd6b25f59782f`.
- `exact_parity_math_elementary_reduced.json`:
  `4f8f351f5d11c27afc0b80b36c180e6f12fa7a90632eea2a709a0dae77a54d61`.

## Histogram implications

Write the nonzero roots of unity in F4 as 1, a, a², with a²+a+1=0. For
histogram (n0,n1,n2), the generating polynomial for elementary symmetric
functions is

```
E(t) = (1+t)^n0 (1+a*t)^n1 (1+a²*t)^n2.
```

When all three counts are 27, E(t)=(1+t³)^27. Consequently every coefficient
whose degree is not divisible by three vanishes, including degrees
1,2,4,8,16 (and the higher powers of two within the degree bound).

Conversely, suppose the counts are nonnegative and sum to 81. Successively
vanishing coefficients at degrees 1,2,4,8,16 force the counts to be congruent
to 27 modulo 2,4,8,16,32, respectively. To see the induction, suppose the
three counts share residue r modulo q=2^j. Write ni=r+q*mi. Frobenius gives

```
E(t) = (1+t³)^r * product_i (1+z_i^q*t^q)^mi.
```

The coefficient at degree q is the sum of (mi mod2)*z_i^q: the first factor
has zero coefficient there because 3 does not divide q, and the second
factor has no positive degree below q. The three values z_i^q are a
permutation of 1,a,a². Their only F2-linear dependence is their total sum,
so vanishing is equivalent to the three next bits being equal. Their sum
81 determines that common bit. Thus the residues are 1,3,3,11,27 at the
successive moduli. At modulus32, each nonnegative count is at least27; their
sum81 forces exactly (27,27,27).

In particular e1=e2=0 forces each count to be 3 modulo4. Four exported e2
constraints, even with their Frobenius partners, do not independently impose
the higher e4/e8/e16 constraints. The complete Fourier ideal is retained.

An independent exhaustive check uses Lucas binomial parity and direct
three-factor coefficient sums, not the generator's recurrence. All 3,403
nonnegative histograms summing to81 agree with the induction. Successive
survivor counts are 820,190,55,10,1.

## Role differences and ordinary squares

For role cell sets A,B, let C=A∩B. The exact ordinary-ring identity is

```
e2(A)+e2(B)+e2(A\B)+e2(B\A)
  = e1(C) * (e1(A)+e1(B)).
```

It follows by splitting A and B into their common and exclusive parts. The
sparse difference e2(A\B)+e2(B\A) equals e2(A)+e2(B) only modulo the existing
unary equations; it is not an unconditional polynomial identity. The audit
checks the nonzero correction polynomial explicitly for all three edges.

The tree T–M, M–L, M–R, together with e2(T), therefore imposes exactly the
four role e2 constraints modulo the retained unary Fourier equations. The
four original term counts are 3240,272,72,72. Fresh set-based Gaussian
elimination of pivots 0,81,90,99 gives exactly the existing free-cell map and
substitutions. Independent ordinary polynomial expansion then matches every
term of the four reduced exports, with counts 3240,2320,144,144.

The reduced quadratics contain 80,32,8,8 ordinary square monomials. They must
remain squared: F4 does not satisfy z²=z. The Frobenius partners square each
polynomial and reduce modulo the retained cubes z³=1. Thus exponent1 becomes2
and exponent2 becomes1. The reduced partners have 80,32,8,8 linear terms and
3160,2288,136,136 quartic terms. All eight partners across original/reduced
exports match independent construction.

The new quadratics raise the vector-space span of the six existing quadratic
Fourier polynomials from rank6 to rank10 after linear elimination. This is a
polynomial-span statement, not a claim of new logical conditions on valid
boards; the new generators already belong to the full ideal.

## Why the quotient is unchanged

Let R=F2[z1,...,z100], let D contain every ordinary domain polynomial z_i³+1,
and let I be the existing Fourier ideal together with D. Each domain splits
into three distinct roots over K=F4: its derivative is z_i² and has no common
root with z_i³+1. Therefore

```
K tensor_(F2) (R/D)  ≅  product over all root assignments of K.
```

Every ideal in this finite product of fields is radical and selects a subset
of the coordinates. The previously proved Fourier/odd-count equivalence says
the surviving coordinates of I are exactly valid labeled boards. Their role
histograms are all (27,27,27), so the new elementary polynomials vanish on
every surviving coordinate. Hence they belong to the scalar-extended ideal.
The map R/I into K tensor_(F2)(R/I) is injective, so they already belong to I.
Adding them leaves the ideal itself unchanged, not merely its point set.
There is consequently no lost multiplicity or change in quotient dimension.

Eliminating the four unary pivots gives an isomorphic quotient only with all
96 free cubic domains and all four substituted pivot-domain polynomials
retained. The reduced model does retain them. The same ideal-equality
argument therefore applies after substitution. Partners add no restriction:
they are squares of already included polynomials, reduced by domain
polynomials that remain in the ideal.

## Independent artifact checks

`exact_elementary_review.py` reconstructs the 81 placements by row indices,
uses set-valued linear elimination and ordinary monomial tuples, strictly
decodes the packed exports, and compares every term. It checks 200 arbitrary
F4 substitution assignments including zero, 200 nonzero free assignments for
the Frobenius identity, and 24 distinct saved valid boards. The known
uniform-triple counterexample also satisfies all e2 constraints, as expected
from its balanced role histograms, while still having only73 distinct T
patterns. This confirms why the augmentation must not replace the Fourier
constraints. Results are in `exact_elementary_review_results.json`.

`exact_elementary_adapter_review.py` additionally audits the actual root
backend definitions and fresh prepare-only files for ordinary row order,
pivot order, reduced40, and reduced80 modes. It reconstructs the appended
equations independently and maps every emitted monomial back through the
inverse original-cell map. Every base polynomial, including all domain
equations, is retained byte-for-byte; exactly eight equations are appended.
Resulting variable/generator counts are 100/188,100/188,96/144,96/180. All
counts retain divisor1 and unrestricted scope. Reduced partner linear terms
are explicitly checked. Non-F2, prefix, binary, fixture, and incompatible
reduced/pivot scopes are rejected. No subprocess can run in these checks.

The adapter's existing `source_sha256` field identifies the final emitted
`.ms` file. The reduced JSON hash remains in `reduced_source_sha256`; the
unaugmented reduced input hash is `base_input_sha256`, distinct from the new
`input_sha256`. The first preparation check incorrectly expected the old
meaning of `source_sha256` after run(); that test assertion was corrected,
and its partial preparation-only files were preserved. Verified fresh
artifacts are under `exact_elementary_adapter_review_prepared_verified`, and
their hashes and terminal PREPARED_NOT_RUN status are recorded in
`exact_elementary_adapter_review_results.json`.
