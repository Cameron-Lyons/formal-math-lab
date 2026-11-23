# Independent review of the Fourier ideal

**No mathematical defect found.** The ordinary polynomial quotient dimension
over `F2` equals the number of full labeled valid ternary boards. This is an
exact reformulation; its numerical dimension remains unevaluated.

Let `K=F2`, `L=F4`, and let `I` be the original exported ideal, including
all 100 equations `z_i^3+1` and the 40 selected Fourier moments.

1. **Domain and multiplicities.** In characteristic two, the derivative of
   `X^3+1` is `X^2`, which is coprime to `X^3+1`. Its three distinct roots
   in `L` are `1,w,w^2`. Thus after scalar extension, the domain quotient
   is the product of one copy of `L` for every labeled coloring. An ideal
   in this finite product of fields removes some factors and leaves the
   others. Consequently `L[z]/I_L` is `L^N`, with no nilpotent multiplicity,
   where `N` is the number of satisfying labeled colorings. This argument
   uses the product-of-fields property, not the false general claim that
   every quotient of a reduced ring is reduced. The related finite étale
   characterization is [Stacks, Lemma 10.143.4](https://stacks.math.columbia.edu/tag/00U3).

2. **Fourier completeness.** On `{1,w,w^2}`, the three character functions
   `1,z,z^2` form an invertible Vandermonde matrix. Its fourfold tensor
   product gives the invertible 81-pattern transform. The uniform parity
   vector has zeroth moment 1 and every nonzero moment 0. The zeroth moment
   is automatic because there are 81 placements. Therefore all 80 nonzero
   moments vanishing is exactly the assertion that each pattern count is
   odd. Nonnegative integer counts with total 81 then all equal one.

3. **Frobenius pairing.** Modulo the domain equations, `P_e^2=P_(2e mod 3)`.
   Doubling pairs the 80 nonzero exponent vectors without fixed points.
   Selecting the vector whose first nonzero entry is 1 keeps exactly one
   member of each pair. Every omitted equation lies in the ideal generated
   by the retained one and the domains; no extra radical operation is
   needed to justify dropping it.

4. **Four-variable elimination.** The four linear moments have rank four.
   The exported substitutions for cells `0,81,90,99` solve them uniquely
   using the other 96 cells. This is an algebra isomorphism, not a
   many-to-one projection. The reduced export retains all 96 free-variable
   domains and all four substituted pivot domains `L_p^3+1`, as well as
   the 36 substituted nonlinear moments. Reduction of exponents modulo
   three is valid modulo these domains. There is no Boolean reduction
   `z^2=z`; exponent two is preserved.

5. **Scalar extension and the count.** Tensoring a finite-dimensional
   `K`-vector space with `L` preserves its dimension over the respective
   field. Hence `dim_K(K[z]/I)=dim_L(L[z]/I_L)=N`. There is no division by
   two for Frobenius, or by twelve for board symmetries. The exports impose
   no palette or reflection normalization. Counting `F2`-rational solutions
   would be a different, incorrect operation: their only possible domain
   coloring is the invalid all-1 coloring. The quotient degree includes
   the degrees of the nontrivial residue fields and correctly counts all
   their `F4` embeddings.

## Independent artifact checks

`exact_parity_review_fourier.py` imports neither the Fourier generator nor
its arithmetic helpers. It implements multiplication in `F4` by polynomial
arithmetic, reconstructs the board windows independently, and performs
ordinary polynomial multiplication modulo explicit `z_i^3+1` relations.

The review checked:

- Every original domain, all 40 original moment polynomials, and the 40
  Frobenius pairs against the JSON exports.
- Rank four of the linear system and the free/pivot variable partition.
- All **40 reduced polynomials symbolically**, including the four pivot
  domains, using general polynomial substitution and multiplication.
- All equations on **60 valid board images**, comprising five published
  seeds under every color permutation and reflection.
- The existing 73-pattern uniform-triple counterexample. Its pivots are
  reconstructed correctly, and it fails **eight original moments and
  eight reduced equations**.

The reduced JSON specifies its 96 free-domain equations in a metadata
string rather than as entries of `remaining_equations`. A consumer must
explicitly add them; loading only that latter list would define the wrong
ideal. The original Singular file uses an ordinary characteristic-two
polynomial ring, which is appropriate.

No counting or standard-basis trial was performed, and none of the math
agent's files were edited. Reviewed input hashes and results are in
`exact_parity_review_fourier_results.json`. Reproduce this review with:

```sh
python experiments/exact_parity_review_fourier.py
```
