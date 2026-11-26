# Exact parity moments and a characteristic-two Fourier ideal

The unrestricted board count equals the vector-space dimension of a concrete
polynomial quotient over **F₂ with 100 variables and 140 generators**, or an
equivalent quotient with **96 variables and 136 generators** after four linear
eliminations. Both ideals are exported below, though their dimensions have
**not** been computed yet. This gives another exact algebraic target, without
claiming that a Gröbner basis computation will finish in practice.

## Why odd counts are sufficient

There are 81 T placements and 81 ordered ternary patterns. If every pattern's
count is odd, every count is at least 1. Because the 81 counts add up to 81,
every count must equal 1. Conversely, a valid board has all counts equal to 1,
which is odd. The same sum argument shows that requiring every pattern to
appear at least once is also enough.

Both equivalences are formalized as `TBoards.ExactParity.valid_iff_odd` and
`valid_iff_present` in [ExactParity.lean](../ExactParity.lean). The file builds
using only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Boolean moment basis

At cell `v`, let `x[v,0]` and `x[v,1]` be the indicator bits for colors 0 and 1.
Over F₂, color 2 has indicator

`δ₂(v)=1+x[v,0]+x[v,1]`.

With Boolean variables, the domain equation `x[v,0]x[v,1]=0` allows exactly
three assignments per cell (`10`, `01`, and `00`), giving a bijection with
ternary boards.

For each of the four T roles, pick either the constant function `1` or one of
the two explicit indicators `δ₀, δ₁`. The resulting `3⁴=81` tensor products
form a basis of functions on the 81 patterns: the three functions `1, δ₀, δ₁`
are linearly independent on one role, so their fourfold tensor matrix is
invertible.

For a tensor product using `k` indicators, a valid board has moment
`3^(4−k)=1` in F₂. The constant moment already equals `81=1`. Requiring the
other **80 moments to equal 1** is therefore equivalent to requiring all 81
pattern counts to be odd. Explicitly, if we expand each pattern indicator with
`δ₂=1+δ₀+δ₁`, its parity becomes a sum of `3^a` constrained moments, which is 1
in F₂. In the reverse direction, summing odd pattern counts over unspecified
roles gives 1 for every moment.

This gives 8 degree-one, 24 degree-two, 32 degree-three, and 16 degree-four
moment equations, plus 100 quadratic cell-domain equations. In an ordinary
polynomial ring, we must also include the 200 Boolean field equations
`x_i²+x_i=0`; a Boolean-polynomial ring builds those in automatically.

## Linear elimination and its precise low-degree limit

Index cell `(row, column)` by `row²+column` and pick four pivot cells:

`0, 81, 90, 99` (the apex, plus the left, middle, and right cells of the last
row).

Their four role-incidence columns are linearly independent, and no T placement
contains two of these cells. That keeps moment substitution from multiplying
two long affine expressions inside a single original monomial. The eight unary
equations solve for both indicator bits at all four cells: the apex and middle
expressions each have 81 affine terms, while the left and right expressions each
have 17 terms.

For either indicator, the left pivot is the XOR of the other terms in the
boundary sum

\[
\sum_{r=1}^{9}\bigl(x_{r,0}+x_{r,2r-1}\bigr)=0,
\]

and the right pivot comes from

\[
\sum_{r=1}^{9}\bigl(x_{r,1}+x_{r,2r}\bigr)=0.
\]

These are the differences between the lower-left/middle and lower-right/middle
unary moments. The apex and center come from the top and middle unary equations.

The exported reduced system has **192 Boolean variables and 172 equations**:
124 quadratics (including all 100 cell-domain equations), 32 cubics, and 16
quartics. It contains 37,110 ANF terms in total, and the largest equation has
6,481 terms. The 96 remaining cells determine the board, though they are not
free: the four reconstructed cells still have to satisfy their kept palette
equations.

We also ran a complete **degree-two Macaulay-span check**. Working modulo
Boolean squares and the 100 forbidden same-cell products leaves 20,001 monomial
columns of degree at most 2. The unary equations and all their variable
multiples have rank 1,572; adding the 24 quadratic moments brings the rank to
1,596. That span contains exactly 8 independent linear relations, all already
present in the unary moments.

So degree-two elimination gives no new linear reductions, and all 24 quadratic
moments stay independent modulo the degree-two unary span. This does **not**
rule out extra linear relations coming from higher-degree products and
cancellations, including those that use the cubic and quartic equations.

Geometry also gives four boundary quadratics: subtracting each `MR` moment from
the matching `LM` moment cancels every interior adjacent pair and leaves only
row-start and row-end pair indicators. Together with six differences among unary
moments, these recover the ten universal local boundary relations found earlier.
They reorganize existing equations rather than adding ten new independent
constraints.

## Homogeneous nonzero-vector coordinates

We can instead encode the three colors as the three nonzero vectors `(a, b)` in
F₂², with domain equation

`1+a+b+ab=0`.

Then `δ₀=1+b`, `δ₁=1+a`, and `δ₂=1+a+b`. Summing either coordinate over the
three colors gives zero, so every nonconstant tensor moment in the basis
`1, a, b` has right-hand side **zero**. All 80 moment polynomials become
homogeneous, and the global palette group becomes `GL(2,2)`. Because this
coordinate change is invertible, the constraint system is unchanged.

## Forty Fourier equations over F₄

Let `F₄=F₂[ω]/(ω²+ω+1)` and encode the three colors as `1, ω, ω²`. Use one
variable `z_v` per cell with the cubic domain `z_v³+1=0`. For each exponent
vector `e ∈ {0, 1, 2}⁴`, define

\[
F_e(z)=\sum_{w\text{ a placement}}\prod_{r=0}^{3}z_{w_r}^{e_r}.
\]

Over `F₄×`, the sums of the 0th, 1st, and 2nd powers are 1, 0, and 0. The
3-by-3 character Fourier matrix is invertible, and so is its fourth tensor
power. Therefore all 81 pattern parities equal 1 if and only if `F_0=1` and
`F_e=0` for every nonzero `e`. The constant equation `F_0=1` holds automatically
because there are 81 placements.

Applying Frobenius gives

\[
F_e^2=F_{2e\bmod3}\quad\pmod{z_v^3+1}.
\]

This pairs up the 80 nonzero exponent vectors into 40 conjugate pairs. Pick the
representative in each pair whose first nonzero entry is 1. Setting these **40
polynomials** to zero is enough to force all 80 to vanish. Their degrees are:

| Degree | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| Equations | 4 | 6 | 10 | 9 | 7 | 3 | 1 |

Each polynomial has 81 terms (3,240 moment terms before reduction). Add the 100
cubic domain equations. Every coefficient lies in **F₂**, so an ordinary
characteristic-two Gröbner backend can work directly over F₂. It must **not**
add the Boolean equations `z_v²+z_v`, which would drop the colors `ω` and `ω²`.

The four degree-one equations solve for cells `0, 81, 90, 99` homogeneously,
with 80, 17, 80, and 17 terms. Because `(Σz)²=Σz²` in characteristic two,
substituting a squared pivot stays sparse as well. The reduced export has 96
free variables, 96 free cubic domains, 36 remaining moments, and 4 substituted
pivot domains, for **136 generators** total. After reduction modulo the free
cubics, the 40 non-free-domain polynomials have 25,070 terms. Every monomial
exponent is stored as 0, 1, or 2.

## Why quotient dimension is the integer count

Over F₄, each cubic `z³+1` has three distinct roots because its derivative `z²`
never vanishes at a root. The quotient by all 100 domain equations is therefore
a finite product of copies of F₄, one for each ternary board. Adding the moment
ideal drops the invalid-board factors and keeps the valid ones. Since an ideal
in a finite product of fields simply deletes factors, no nilpotent
multiplicities appear, and the quotient's F₄-vector-space dimension equals the
number of valid boards.

Because all generators have coefficients in F₂, extending scalars from F₂ to F₄
keeps the finite vector-space dimension the same. So the **F₂-vector-space
dimension of the exported ordinary polynomial quotient is that exact integer
count**. Linear elimination gives an isomorphic quotient, so the reduced ideal
has the same dimension.

Given a complete Gröbner or standard basis, we could count the standard
monomials of its leading ideal using arbitrary-precision integers. A completed
standard basis is essential: counting initial terms of an arbitrary generating
set does not give the quotient dimension. See
[Singular's documentation for quotient vector-space dimension](https://www.singular.uni-kl.de/Manual/latest/sing_381.htm).
For the separate Boolean system, [PolyBoRi](https://polybori.sourceforge.net/)
supports specialized Boolean polynomial storage and Gröbner computations; we
list it only as a possible backend and have not run it here.

## Executable checks and exports

The binary version has 25 bits and 15 moments, reducing under the same boundary
elimination to 21 bits and 11 equations. Checking **all 2,097,152 reduced
assignments** against direct pattern distinctness gave **168 solutions and zero
mismatches** in about 0.235 seconds.

For ternary boards, both exports accept all 322 independently checked valid
boards. Each export's substitution identities were also checked equation by
equation on 100 deterministic random assignments of the free cells. The Boolean
tensor matrix has rank 81 over F₂, and the Fourier matrix has rank 81 over F₄.

The earlier triple-marginal counterexample satisfies **79 of the 80 Boolean
moment equations**, failing only the degree-four moment with color 1 in all four
roles. That shows the missing quartic does not follow from the other 79 moments
even on actual boards. This counterexample is formalized in
[MarginalCounterexample.lean](../MarginalCounterexample.lean).

Files:

* [exact_parity_math.py](exact_parity_math.py): moment generation, rank checks,
  boundary elimination, and Boolean exports.
* [exact_parity_math_reduced_3.json](exact_parity_math_reduced_3.json): 192-bit
  ternary ANF system; [analysis results](exact_parity_math_results.json).
* [exact_parity_math_binary.cpp](exact_parity_math_binary.cpp): exhaustive binary
  audit; [saved result](exact_parity_math_binary_result.json).
* [exact_parity_math_check.py](exact_parity_math_check.py): Boolean export audit;
  [saved result](exact_parity_math_check_results.json).
* [exact_parity_math_fourier.py](exact_parity_math_fourier.py): Fourier exports
  and checks; [saved result](exact_parity_math_fourier_results.json).
* [Original Fourier JSON](exact_parity_math_fourier_original.json): explicit
  cell and exponent pairs for every term and all 100 domains.
* [Original Singular ideal](exact_parity_math_fourier_original.sing): ring and
  ideal declarations only; loading it starts no basis computation.
* [Reduced Fourier JSON](exact_parity_math_fourier_reduced.json): free-cell map,
  pivot substitutions, implicit free cubic domains, and 40 remaining equations.

Reproduction:

```sh
python experiments/exact_parity_math.py
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_parity_math_binary.cpp -o /tmp/exact_parity_math_binary
/tmp/exact_parity_math_binary experiments/exact_parity_math_reduced_2.dat > experiments/exact_parity_math_binary_result.json
python experiments/exact_parity_math_check.py
python experiments/exact_parity_math_fourier.py
```

Small fixtures for testing an ordinary-polynomial backend before trying the full
ideal: `F₂[z]/(z³+1)` has dimension 3; two independent cubic domains give
dimension 9; adding `z₀+z₁` drops it to 3. Three cubic domains plus
`z₀+z₁+z₂=0` give dimension 6, since the three nonzero F₄ colors must all
differ. These fixtures separate this cubic-domain encoding from Boolean
counting.
