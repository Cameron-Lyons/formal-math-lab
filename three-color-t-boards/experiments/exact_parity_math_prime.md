# The exact Fourier ideal in other prime characteristics

For every prime `p≡2 (mod 3)`, the original Fourier ideal with domains
`z_v³−1` and the same 40 representative moment sums has quotient dimension
equal to the unrestricted ternary-board count. This includes **p=29** and
**p=83**. No full instance was run for this analysis.

## Proof of the count identity

Let `K=F_p[ω]/(ω²+ω+1)`. The quadratic is irreducible because `F_p×` has order
`p−1`, not divisible by three; hence it contains no nontrivial cube root of
unity. Thus `K=F_{p²}`, and the three color values are `1,ω,ω²`, with
`ω²=−1−ω`.

Frobenius exchanges the two nontrivial cube roots. On the domain equations,

\[
F_e(z)^p=F_{pe\bmod3}(z)=F_{2e\bmod3}(z).
\]

The 40 chosen representatives therefore force all 80 nonconstant Fourier
coordinates to vanish. The constant coordinate is **81 modulo p**, not
generally one. Fourier inversion is valid because `3`, and hence `81`, is
invertible in characteristic `p`. It gives every pattern occurrence count

\[
n_s\equiv81/81\equiv1\pmod p.
\]

Every `n_s` is a nonnegative integer. Since `p>1`, this residue excludes zero,
so all 81 counts are at least one. Their sum is 81, forcing each to equal one.
The converse is immediate. This saturation statement is also formalized for
every modulus greater than one as
`TBoards.ExactParity.valid_iff_congruent_one` in
[ExactParity.lean](../ExactParity.lean).

The cubic domains are squarefree because `p≠3`, and all their roots lie in
`K`. Over `K`, the domain quotient is a product of fields indexed by ternary
boards. Adding the moments retains exactly the valid-board factors, so its
dimension is the board count. All generators have coefficients in `F_p`;
scalar extension preserves dimension, proving the same statement for the
ordinary polynomial quotient over **F_p**.

The restriction `p≡2 mod3` matters when retaining only 40 moments. For primes
`p≡1 mod3`, Frobenius fixes the cube roots and does not supply the omitted
conjugate moments. Using all 80 moments would restore the proof for every
prime other than three.

## Earlier exact marginal balance

For a fixed subset of `k` roles, impose all Fourier moments supported in that
subset. Fourier inversion gives each of its `3^k` marginal counts the residue

\[
n_s\equiv3^{4-k}\pmod p.
\]

If `p>3^(4−k)`, every nonnegative count is at least `3^(4−k)`. Since their sum
is 81, all are exactly equal to that target. Therefore:

| Layer | Target per marginal pattern | Sufficient threshold | Smallest prime `p≡2 mod3` above it |
|---|---:|---:|---:|
| Unary | 27 | `p>27` | 29 |
| Pair | 9 | `p>9` | 11 |
| Triple | 3 | `p>3` | 5 |
| Full pattern | 1 | `p>1` | 2 |

Thus 29 is the smallest prime in this family for which **the unary equations
alone** enforce exact role histograms. Characteristic 83 is unnecessary for
that property. At 23, unary residue constraints still allow, for example,
counts `(4,4,73)`; at 29 they allow only `(27,27,27)`.

There is a useful distinction: characteristic five already enforces every
proper marginal once **all triple-support moments** are present, because
exact lower marginals follow by summing exact triple marginals. The benefit
of 29 is that exact unary balance is present at the linear layer, and exact
pair balance at the pair layer. This strengthens low-order constraints but
does not prove a faster Gröbner computation. Exact proper marginals alone
still admit the existing invalid-board witness.

## Conversion hazards

The original exported moment list is reusable: the checker verified that each
of its 40 polynomials has exactly 81 distinct monomials with integer
coefficient one. Although it was generated with an F₂ data structure, no
original moment terms cancelled. Its domain declarations must be changed to
the intended `z³−1`.

Keeping `z³+1` in odd characteristic instead represents the three cube roots
of minus one. The unconditioned homogeneous system is still equivalent under
global substitution `z→−z`, but fixed-prefix constants and interpretation
must also change. Using `z³−1` throughout avoids that mismatch.

The F₂ **reduced** export cannot be reinterpreted directly in characteristic
29. Linear substitution signs change, coinciding terms must add modulo 29
rather than cancel by XOR, and `(Σz)²=Σz²` is false in odd characteristic.
Likewise, fixed color two is `ω²=−1−ω`, represented by coefficient pair
`(p−1,p−1)`, not `(1,1)`. Prefix term coefficients require ordinary modular
field addition and multiplication.

There is an additional elimination trap. Frobenius can express a valid
pivot's conjugate as a sum of conjugated free variables, but replacing its
cubic domain with a norm-one equation is insufficient: the norm-one subgroup
of `F_{p²}×` has **p+1** elements. At 29 that admits 30 possibilities instead
of three. Retain or correctly rederive every cubic pivot-domain condition.

## Exact small fixtures

These dimensions hold for every prime `p≡2 mod3` and follow by enumerating the
three cube roots in `F_{p²}`:

* One domain `z³−1`: dimension 3.
* Two independent domains: dimension 9.
* Two domains plus `z₀−z₁`: dimension 3.
* One domain plus `z²+z+1`: dimension 2.
* Three domains plus `z₀+z₁+z₂`: dimension 6; the three colors must all differ.
* Over `F_{p²}`, one domain plus `z−ω²`: dimension 1.

For odd `p`, two domains plus **`z₀+z₁`** instead have dimension zero, so that
fixture catches an accidental characteristic-two sign convention.

[exact_parity_math_prime.py](exact_parity_math_prime.py) independently checks
the field arithmetic, Fourier orthogonality, conjugacy, fixtures, and marginal
thresholds at primes 2,5,11,17,23,29,83. It also audits the original JSON's
distinct coefficient-one terms. Results are saved in
[exact_parity_math_prime_results.json](exact_parity_math_prime_results.json).
These are finite algebra checks, not an evaluation of the full count.
