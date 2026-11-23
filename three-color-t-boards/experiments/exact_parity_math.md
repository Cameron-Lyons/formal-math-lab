# Exact parity moments and a characteristic-two Fourier ideal

The unrestricted count is exactly the vector-space dimension of a concrete
polynomial quotient over **F₂ with 100 variables and 140 generators**, or an
equivalent quotient with **96 variables and 136 generators** after four linear
eliminations. These ideals are exported below. Their dimensions have **not**
been evaluated. The reduction provides a different exact algebraic backend
target; it does not establish that a Gröbner computation will be practical.

## Why odd counts are sufficient

There are 81 placements and 81 possible ordered ternary patterns. If every
pattern's occurrence count is odd, every count is at least one. Since their
sum is 81, all 81 counts equal one. Conversely, a valid board has all counts
odd. The same saturation argument shows that merely requiring every pattern
to occur is sufficient.

The parent investigation formalized these statements as
`TBoards.ExactParity.valid_iff_odd` and `valid_iff_present` in
[ExactParity.lean](../ExactParity.lean). Its successful build uses only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Boolean moment basis

At cell `v`, let `x[v,0]` and `x[v,1]` indicate colors 0 and 1. Over F₂,

`δ₂(v)=1+x[v,0]+x[v,1]`.

The domain equation `x[v,0]x[v,1]=0`, together with Boolean variables, gives
exactly three assignments per cell: `10`, `01`, `00`. Thus there is a
bijection with ternary boards.

For each of four roles choose either the constant function or one of the two
explicit indicators. The resulting `3⁴=81` tensor functions are a basis of
functions on the 81 patterns. At one role the three functions `1,δ₀,δ₁` are
independent; their fourfold tensor matrix is therefore invertible.

For a choice involving `k` indicators, a valid board's moment is
`3^(4−k)=1` in F₂. The constant moment already equals `81=1`. Requiring the
remaining **80 moments to equal one** is equivalent to requiring all 81
pattern counts odd. Explicitly, expand each occurrence indicator using
`δ₂=1+δ₀+δ₁`; its parity becomes a sum of `3^a` constrained moments, hence one.
The converse follows by summing odd pattern counts over unspecified roles.

There are 8 degree-one, 24 degree-two, 32 degree-three, and 16 degree-four
moment equations, plus 100 quadratic cell-domain equations. In an ordinary
polynomial ring one must also include the 200 Boolean field equations
`x_i²+x_i=0`; a Boolean-polynomial ring includes these automatically.

## Linear elimination and its precise low-degree limit

Flatten cell `(row,column)` to `row²+column`. Choose cells

`0, 81, 90, 99`: the apex and the left, middle, right cells of the last row.

Their four role-incidence columns are independent. No T contains two of these
cells, which prevents moment substitution from multiplying two long affine
expressions in a single original monomial. The eight unary equations solve
both indicator bits at all four cells. The apex and middle solutions each
have 81 affine terms, while the left and right solutions each have 17 terms.

For either indicator, the left solution is the XOR of the other entries in
the boundary sum

\[
\sum_{r=1}^{9}\bigl(x_{r,0}+x_{r,2r-1}\bigr)=0,
\]

and the right solution uses

\[
\sum_{r=1}^{9}\bigl(x_{r,1}+x_{r,2r}\bigr)=0.
\]

These are the differences of lower-left/middle and lower-right/middle unary
moments. The apex and center use the top and middle unary equations.

The export has **192 Boolean variables and 172 equations**: 124 quadratics
(including all 100 cell-domain conditions), 32 cubics, and 16 quartics. It
contains 37,110 ANF terms; the largest equation has 6,481 terms. The 96
remaining cells can parameterize assignments, but their assignments are
constrained: in particular, the four reconstructed cells must satisfy their
retained palette equations.

A complete **degree-two Macaulay-span check** was also performed. Work modulo
Boolean squares and the 100 forbidden same-cell products. Among the 20,001
remaining monomial columns of degree at most two, the unary equations and all
their variable multiples have rank 1,572. Adding the 24 quadratic moments
raises the rank to 1,596. The resulting span contains exactly eight independent
linear relations, all already supplied by unary moments.

Thus this degree-two elimination supplies no further linear reduction, and
all 24 quadratic moments remain independent modulo that span. This does **not**
exclude linear consequences obtained through higher-degree products and
cancellations, including use of the cubic and quartic equations.

Geometry also gives four boundary quadratics: the difference of each `LM`
moment and the matching `MR` moment cancels all interior adjacent pairs,
leaving row-start and row-end pair indicators. Along with six differences
among unary moments, these recover the previously identified ten universal
local boundary relations. They reorganize the same equations; they do not
provide ten extra independent constraints.

## Homogeneous nonzero-vector coordinates

Encode colors instead as the three nonzero vectors `(a,b)` in F₂². Their
domain equation is

`1+a+b+ab=0`.

The old indicators become `δ₀=1+b`, `δ₁=1+a`, `δ₂=1+a+b`. Over the three
colors, either coordinate sums to zero. Therefore every nonconstant tensor
moment in the basis `1,a,b` has right-hand side **zero**. All 80 moment
polynomials are homogeneous, and the global palette group becomes the linear
group `GL(2,2)`. This is an invertible change of coordinates, not a weaker
condition.

## Forty Fourier equations over F₄

Let `F₄=F₂[ω]/(ω²+ω+1)` and encode the three colors by `1,ω,ω²`. Use one variable
`z_v` per cell and impose `z_v³+1=0`. For an exponent vector
`e∈{0,1,2}⁴`, define

\[
F_e(z)=\sum_{w\text{ a placement}}\prod_{r=0}^{3}z_{w_r}^{e_r}.
\]

On `F₄×`, the sums of the powers 0, 1, 2 are respectively 1, 0, 0. The
three-character Fourier matrix is invertible, and so is its fourth tensor
power. Consequently all pattern parities are one exactly when `F_0=1` and
`F_e=0` for every nonzero `e`. The constant condition is automatic because
there are 81 placements.

Frobenius supplies

\[
F_e^2=F_{2e\bmod3}\quad\pmod{z_v^3+1}.
\]

The 80 nonzero exponent vectors split into 40 conjugate pairs. Choose the
representative whose first nonzero coordinate is 1. Requiring these **40
polynomials** to vanish therefore suffices. Their degree counts are

| Degree | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| Equations | 4 | 6 | 10 | 9 | 7 | 3 | 1 |

Each has 81 terms, for 3,240 original moment terms. Add the 100 cubic domain
equations. All polynomial coefficients are in **F₂**, so an ordinary
characteristic-two Gröbner backend can work directly over F₂. It must **not**
add Boolean equations `z_v²+z_v`: those would discard the colors `ω,ω²`.

The four degree-one equations solve cells `0,81,90,99` homogeneously, with
80,17,80,17 summands respectively. Since `(Σz)²=Σz²`, substituting a squared
pivot also remains sparse. The reduced export has 96 free variables, 96 free
cubic domains, 36 remaining moments, and four substituted pivot domains:
**136 generators**. The 40 non-free-domain polynomials have 25,070 terms after
reduction modulo the free cubics. Every monomial exponent is stored as 0,1,2.

## Why quotient dimension is the integer count

Over F₄, each `z³+1` has three distinct roots: its derivative is `z²`, nonzero
at every root. Hence the quotient by all 100 domains is a finite product of
copies of F₄, one per ternary board. Adding the moment ideal removes exactly
the invalid-board factors. An ideal in a finite product of fields simply
removes factors, so no nilpotent multiplicities appear. The quotient's
F₄-vector-space dimension is therefore the number of valid boards.

All generators have F₂ coefficients. Scalar extension from F₂ to F₄ preserves
finite vector-space dimension. Thus the **F₂-vector-space dimension of the
exported ordinary polynomial quotient is the same integer count**. Linear
elimination preserves the quotient up to isomorphism, so the reduced ideal
has the same dimension.

A complete Gröbner/standard basis would permit counting standard monomials
of the leading ideal. That final count must use arbitrary-precision integers.
The standard-basis requirement matters: counting initial terms of an arbitrary
generating set does not compute quotient dimension. [Singular's primary
documentation for quotient vector-space dimension](https://www.singular.uni-kl.de/Manual/latest/sing_381.htm).
For the separate Boolean formulation, PolyBoRi offers specialized Boolean
polynomial storage and Gröbner computations; this is a possible backend, not
an evaluated result here. [PolyBoRi's project description](https://polybori.sourceforge.net/).

## Executable checks and exports

The binary analogue has 25 bits and 15 moments. The same boundary elimination
leaves 21 bits and 11 equations. Exhaustively checking **all 2,097,152 reduced
assignments** against direct geometric distinctness gave **168 solutions and
zero mismatches**, in approximately 0.235 seconds.

For ternary boards, both exports accept 322 independently checked valid boards.
Each export's substitution identities were also compared equation by equation
on 100 deterministic random assignments of its free cell colors. The Boolean
tensor matrix has rank 81 over F₂ and the Fourier matrix has rank 81 over F₄.

The earlier triple-marginal counterexample satisfies **79 of the 80 Boolean
moment equations**; its only failure is the degree-four moment with color 1
in every role. Thus the omitted quartic is not recovered even from all the
other moments on actual boards. The witness is already formalized in
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
  cell/exponent pairs for every term and all 100 domains.
* [Original Singular ideal](exact_parity_math_fourier_original.sing): ready
  ring and ideal declarations only; loading it launches no basis computation.
* [Reduced Fourier JSON](exact_parity_math_fourier_reduced.json): free-cell map,
  pivot substitutions, implicit free cubic domains, and 40 remaining equations.

Reproduction:

```sh
python experiments/exact_parity_math.py
c++ -O3 -std=c++20 experiments/exact_parity_math_binary.cpp -o /tmp/exact_parity_math_binary
/tmp/exact_parity_math_binary experiments/exact_parity_math_reduced_2.dat > experiments/exact_parity_math_binary_result.json
python experiments/exact_parity_math_check.py
python experiments/exact_parity_math_fourier.py
```

Small ordinary-polynomial backend fixtures: `F₂[z]/(z³+1)` has dimension 3;
two independent cubic domains give dimension 9; adding `z₀+z₁` gives dimension
3. Three cubic domains plus `z₀+z₁+z₂=0` give dimension 6: the three nonzero
F₄ colors must all differ. These fixtures distinguish this formulation from
Boolean-variable counting before attempting the unevaluated full ideal.
