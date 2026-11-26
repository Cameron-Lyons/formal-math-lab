# The exact Fourier ideal in other prime characteristics

For any prime `p ≡ 2 (mod 3)`, the original Fourier ideal with cubic domains
`z_v³−1` and the same 40 representative moment sums has quotient dimension equal
to the unrestricted ternary board count. This includes **p=29** and **p=83**.
No full solver run was performed for this note.

## Proof of the count identity

Let `K=F_p[ω]/(ω²+ω+1)`. Because `F_p×` has order `p−1`, which is not divisible
by 3, `F_p` has no nontrivial cube root of unity and `ω²+ω+1` is irreducible.
Thus `K=F_{p²}`, and the three color values are `1, ω, ω²` with `ω²=−1−ω`.

Frobenius swaps the two nontrivial cube roots. Modulo the domain equations,

\[
F_e(z)^p=F_{pe\bmod3}(z)=F_{2e\bmod3}(z).
\]

Setting the 40 representatives to zero therefore forces all 80 nonconstant
Fourier coordinates to vanish. The constant coordinate equals **81 modulo p**,
not 1 in general. Because `3` (and so `81`) is invertible in characteristic `p`,
Fourier inversion applies and gives every pattern count

\[
n_s\equiv81/81\equiv1\pmod p.
\]

Every `n_s` is a nonnegative integer. Since `p>1`, congruence to 1 rules out
zero, so every count is at least 1. Because all 81 counts sum to 81, every
count equals 1. The converse is immediate. This saturation argument is
formalized for every modulus above 1 as
`TBoards.ExactParity.valid_iff_congruent_one` in
[ExactParity.lean](../ExactParity.lean).

Because `p≠3`, each cubic domain is squarefree and splits completely over `K`.
The domain quotient over `K` is a product of copies of `K`, one per ternary
board. Adding the moment equations keeps only the valid-board factors, so its
dimension is the board count. Every generator has coefficients in `F_p`, and
scalar extension preserves dimension, so the ordinary polynomial quotient over
**F_p** has the same dimension.

The condition `p ≡ 2 (mod 3)` is needed when keeping only 40 moments. When
`p ≡ 1 (mod 3)`, Frobenius fixes the cube roots and does not generate the
missing conjugate moments. Keeping all 80 moments makes the proof work for every
prime other than 3.

## Earlier exact marginal balance

Suppose we impose all Fourier moments supported on a subset of `k` roles.
Fourier inversion forces each of its `3^k` marginal counts to satisfy

\[
n_s\equiv3^{4-k}\pmod p.
\]

When `p > 3^(4−k)`, every nonnegative count must be at least `3^(4−k)`. Since
the counts add up to 81, all of them must equal that target:

| Layer | Target per marginal pattern | Sufficient threshold | Smallest prime `p ≡ 2 (mod 3)` above it |
|---|---:|---:|---:|
| Unary | 27 | `p>27` | 29 |
| Pair | 9 | `p>9` | 11 |
| Triple | 3 | `p>3` | 5 |
| Full pattern | 1 | `p>1` | 2 |

So 29 is the smallest prime in this family where **the unary equations alone**
force exact role histograms; characteristic 83 adds nothing there. At `p=23`,
unary residues still allow counts like `(4, 4, 73)`; at `p=29`, they allow only
`(27, 27, 27)`.

One nuance: characteristic 5 already forces every proper marginal once all
triple-support moments are included, because summing exact triple marginals
gives exact lower marginals. The advantage of 29 is that exact unary balance
appears already at the linear layer and exact pair balance at the pair layer.
That strengthens low-degree constraints, though it does not guarantee a faster
Gröbner basis computation, and exact proper marginals alone still admit the
known invalid-board counterexample.

## Conversion hazards

The original exported moment list can be reused directly: the checker verified
that each of its 40 polynomials has 81 distinct monomials with integer
coefficient 1, so nothing canceled modulo 2 when it was generated. Only the
domain equations need to switch from `z³+1` to `z³−1`.

Keeping `z³+1` in odd characteristic instead represents the three cube roots of
`-1`. The unconditioned homogeneous system stays equivalent under `z → −z`, but
fixed-prefix constants and their color mapping would also have to change. Using
`z³−1` everywhere avoids that sign mismatch.

By contrast, the F₂ **reduced** export cannot be reused directly in
characteristic 29. Linear substitution signs change, coinciding terms add
modulo 29 instead of canceling by XOR, and `(Σz)²=Σz²` fails in odd
characteristic. Fixed color 2 is `ω²=−1−ω`, stored as `(p−1, p−1)` rather than
`(1, 1)`, and prefix coefficients need ordinary modular field arithmetic.

There is also an elimination trap. Frobenius writes a valid pivot's conjugate
as a sum of conjugated free variables, yet replacing the pivot's cubic domain
with a norm-one equation is too weak: the norm-one subgroup of `F_{p²}×` has
**p+1** elements (30 values at `p=29` instead of 3). Keep or rederive every
cubic pivot-domain equation.

## Exact small fixtures

For every prime `p ≡ 2 (mod 3)`, counting the three cube roots in `F_{p²}`
gives these quotient dimensions:

* One domain `z³−1`: dimension 3.
* Two independent domains: dimension 9.
* Two domains plus `z₀−z₁`: dimension 3.
* One domain plus `z²+z+1`: dimension 2.
* Three domains plus `z₀+z₁+z₂`: dimension 6 (all three colors must differ).
* Over `F_{p²}`, one domain plus `z−ω²`: dimension 1.

For odd `p`, two domains plus **`z₀+z₁`** give dimension 0, which catches an
accidental characteristic-two sign convention.

[exact_parity_math_prime.py](exact_parity_math_prime.py) independently checks
the field arithmetic, Fourier orthogonality, conjugacy, fixtures, and marginal
thresholds at primes `2, 5, 11, 17, 23, 29, 83`, and audits the original JSON's
distinct coefficient-one terms. Results are in
[exact_parity_math_prime_results.json](exact_parity_math_prime_results.json).
These are finite algebra checks and do not evaluate the full board count.
