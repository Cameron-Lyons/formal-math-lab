# Pell families with pole order at most two in x

Suppose a nonsplit Pell conic over `ℚ` has a rational point, and `x,y,z` are rational functions on it defined over `ℚ` with poles allowed only at the two conjugate points at infinity. Suppose they satisfy `z²+y²z+x³=2` identically and take integer values together at one rational point. **If x has pole order at most two at infinity, the family is constant.**

The proof below uses finite enumeration and local lifting. Lean checks the pole-order-one obstruction, the characteristic-zero constant-fiber argument, the leading-coefficient and square-factor arguments, the polynomial specialization steps, uniqueness at a nonsingular residue class, and the even-quadratic obstruction. The construction of the ramified extension, the coordinate changes on the conic and the positive-characteristic constant-fiber argument are given below. A C++ program verifies the finite enumerations. [Pole order one](PoleOne.lean) · [Constant fibers](PellConstantFiber.lean) · [Leading coefficients and square factor](PoleTwo.lean) · [Specialization](PoleTwoReduction.lean) · [Uniqueness](PoleTwoLifting.lean) · [Even-quadratic obstruction](SmallCubic.lean) · [Finite checker](pole_two_check.cpp)

## The possible pole orders

All nonconstant functions defined over `ℚ` and regular on the affine conic have poles of equal positive order at its two conjugate ends. Write `K=ℚ(√D)` for the splitting field, with `D` a squarefree integer. Over `K` the affine coordinate ring is `K[T,T⁻¹]`. Center the norm parameter at the given integral point, so that point has `T=1` and conjugation takes `T` to `1/T`. Translating by the seed also identifies a Pell conic of nonunit norm with the norm-one conic.

Put `z′=z+y²`. Every irreducible factor of a Laurent polynomial `z` at a nonzero finite point has degree divisible by three over `K`. Indeed at its root, `x³=2`, and the cubic `X³−2` is irreducible over a quadratic number field. The polynomial `Tᵐz` for a function of pole order `m` has degree `2m` and nonzero constant term. Consequently `3|m`. The same applies to `z′`.

A constant `x` makes `zz′=2−x³` a nonzero constant. Both factors must then be units of the Laurent ring, and conjugation shows a rational Laurent unit is constant. A constant `z` gives a constant triple as well. For a nonzero rational constant `z` the equation `z y²=2−z²−x³` defines a smooth genus-one curve since `z²≠2`. A nonconstant parametrization would embed its function field in a rational function field, contrary to Lüroth's theorem. For constant `z′` apply the same argument to `−z′`, the other root in `z`. A constant `y` gives the same genus-one argument using `w=2z+y²` and `w²=y⁴+8−4x³`, since `y⁴+8≠0`.

Thus in a nonconstant family the positive pole orders of `z,z′` are multiples of three adding to three times that of `x`. Pole order one for `x` is impossible. Pole order two forces orders `3,3` for `z,z′`, at most one for `y` from `y²=z′−z`, and exactly three for `w`. We henceforth have Laurent supports `[-2,2], [-1,1], [-3,3]` for `x,y,w`, with nonzero outer coefficients.

## Integral coefficients at 13

Work at a place over 13. We use two polynomial enumeration results proved computationally below.

1. Over `F₁₃`, every polynomial solution of `w²=y⁴+8−4x³` with `deg x≤4, deg y≤2` is constant.
2. Over either `F₁₃` or `F₁₆₉`, the same holds for `deg x≤2, deg y≤1`.

In the rational coordinate `s` with `T=(1+√D s)/(1−√D s)`, put `Q=1−Ds²`. The three functions are `X/Q²,Y/Q,W/Q³` with rational polynomial numerators of degrees at most `4,2,6`. This follows by substituting the displayed fraction in the Laurent sums and using invariance under conjugation. The three constant terms are integers, by the seed at `s=0`. The polynomial identity is

```text
W² + 4X³ = Y⁴ Q² + 8 Q⁶.
```

Suppose some numerator coefficient has negative valuation. Normalize the valuation by `v(π)=1`. Set `h=max(−v(aᵢ)/i)` over all nonzero numerator coefficients of positive index, so `h>0`. Choose `λ` of valuation `h` in a totally ramified extension, adjoining an appropriate root of a uniformizer. Substituting `s=λS` makes all coefficients integral and leaves a positive-degree numerator term a unit. The denominator polynomial reduces to `1`. Reduction would give a nonconstant polynomial solution violating result 1. Hence all numerator coefficients are integral.

`coefficient_balancing_slope` proves that this maximum is positive, yields nonnegative adjusted valuations, and attains zero at a positive index. In Mathlib's multiplicative valuation convention, `specialize_pole_two_at_a_slope` then takes `λ` satisfying the balancing inequalities and proves the residue identity, nonconstancy and all degree bounds. It constructs the scaled integral polynomials from the original numerator coefficients.

In the local splitting field use `s′=√D s`, for which the denominator is `1−s′²`. If 13 is unramified, `√D` is a unit and the new coefficients are integral. If 13 ramifies, the residue field is still `F₁₃`, and the same shrinking argument applied in `s′` establishes integrality again. Finally substitute `s′=(T−1)/(T+1)`. Since `1−s′²=4T/(T+1)²` and 2 is a unit, every Laurent coefficient of `x,y,w` is integral.

These Laurent polynomials cannot all reduce to constants. If they did, let `h=min(v(aᵢ)/i)` over their nonzero coefficients of positive index. This set is nonempty, and `h>0`. Substitute `T=λ⁻¹U` for an element of valuation `h` in a totally ramified extension. Negative powers then disappear in the reduction, while a positive power survives. The result is a nonconstant ordinary polynomial solution in the residue field contradicting result 2. Moreover `y` itself must reduce to a nonconstant Laurent polynomial. For constant residue `y₀`, the cubic `w²=y₀⁴+8−4x³` is smooth of genus one, and Lüroth again applies. The checker verifies `y₀⁴+8≠0` for every element of both residue fields. This deals also with inseparable maps, since Lüroth does not require separability.

There is an elementary way to see the constant-`y` step at these degrees. Write `δ=T d/dT`. On the smooth fiber `w²=C−4x³` with `C≠0`, a nonconstant `x` would give a nonzero `w`. The function `δx/w=−δw/(6x²)` has no finite nonzero poles, since `x,w` never vanish together. At an end where `x` is regular, `w,δx,δw` are also regular, so one of these two expressions is regular. At an end where `x` has a pole of order `m>0`, the pole of `w` has order `3m/2`, while the pole order of `δx` is at most `m`. The quotient is therefore globally regular and has a zero, so it vanishes identically. This implies `δx=0`, which forces `x` to be constant because all exponents have absolute value less than 13. The identical argument works for the ordinary polynomial searches.

For the change toward a pole, `specialize_pole_two_towards_infinity` starts with the rescaled integral numerators, the coefficient valuations found by the minimum-slope argument, and their cleared identity. It removes the Laurent denominators and proves the ordinary residue identity, its nonconstancy and the reduced degree bounds.

## Loss of a pole on reduction

At either end write `x₂,x₁,…` and `w₃,w₂,…` for the leading Laurent coefficients at that end. Terms of order six and five give

```text
w₃² = −4x₂³,       2w₃w₂ = −12x₂²x₁.
```

Here `x₂,w₃` are nonzero in characteristic zero. Taking `s=−w₃/(2x₂)` gives `s²=−x₂, w₃=2s³, w₂=−3s x₁`. In particular `s` is integral. If `x₂` vanishes in the residue field, so do `s,w₃,w₂`. The coefficient of order four then gives `y₁⁴=0`. Hence at each end where `y` keeps a pole, `x` keeps its full pole order. The implication applies independently to the two ends. These are the first two lemmas in `PoleTwo.lean`.

## Finite searches

The checker uses ordinary power-basis arithmetic in `F₁₃` and `F₁₆₉=F₁₃[√2]`. It first rejects some candidates by point evaluation, then reconstructs a candidate polynomial square root coefficient by coefficient and checks the identity by multiplication.

For the ordinary searches, normalize nonconstant linear `y` to `T` by an affine change of variable. Over `F₁₃` a nonconstant quadratic normalizes to `dT²+b` with `d=1` or `2`, representing the two nonzero square classes. The program enumerates every allowed `x`. Constant `y` is covered by the genus-one argument above.

For Laurent reduction, reverse the order of the ends if necessary so that `y` has a pole at infinity. Scale `T` by its leading coefficient, a unit, and write

```text
y = T + b + c/T,   X=T²x,   Y=Ty,   W=T³w.
W² = T²Y⁴ + 8T⁶ − 4X³.
```

Over prime residue field the checker tries every `b,c∈F₁₃`, including `c=0`, and every `X` allowed by the leading coefficient equations. In particular `X₄≠0`, while `X₀=0` is allowed when `c=0`. A nonzero extreme coefficient of `X` must be a square in the residue field since `−4` is a square there and `w₃²=−4x₂³`.

In the unramified inert case the outer coefficients of the original `y` are conjugate. Their product `c` is a nonzero norm in `F₁₃`, and `b∈F₁₃`. In the normalized coordinate the coefficients of `x` have `x₋ⱼ=cʲ conjugate(xⱼ)`. Thus the program enumerates `x₂,x₁∈F₁₆₉` and `x₀∈F₁₃`. At test points of norm `c`, all three Laurent functions take values in `F₁₃`, so a legitimate discriminant takes a square value in that subfield. The ramified case was already included in the prime-residue-field check.

| Field and search | Candidate pairs | Square discriminants |
|---|---:|---:|
| Ordinary, 13 elements | 10,024,911 | 0 |
| Ordinary, 169 elements | 4,826,809 | 0 |
| Laurent, 13 elements | 13,537,914 | 6 |
| Laurent with conjugate coefficients, 169 elements | 28,789,488 | 12 |

## Lifting and descent

Every Laurent hit has `c≠0`. Fix this parameter. There are thirteen remaining coefficients, namely `b`, the five coefficients of `X` and the seven of `W`. The checker proves for each hit that the thirteen coefficient equations have an invertible Jacobian in these variables. The columns are the coefficient vectors of `−4T³Y³`, `12TⁱX²` for `0≤i≤4`, and `2TⁱW` for `0≤i≤6`. Opposite choices of sign for `W` have identical invertibility and symmetries.

Two integral solutions with the same exact `c` and the same reduction therefore coincide. To see this, express each difference of polynomial values as a row times the vector of input differences. Modulo the maximal ideal each row equals the corresponding Jacobian row. The resulting matrix has nonzero determinant and trivial kernel over the valuation ring, so the two input vectors agree. Lean proves this for a square polynomial system of any finite dimension. [Uniqueness of the lift](PoleTwoLifting.lean)

At each hit the checker also verifies invariance of the triple under both operations

```text
(x(T), y(T), w(T)) ↦ ( x(−T), −y(−T), −w(−T) )
(x(T), y(T), w(T)) ↦ ( x(c/T), y(c/T), −w(c/T) ).
```

They are integral operations on coefficients since `c` is a unit, and both preserve the coefficient equations and the same exact `c`. Uniqueness now gives these symmetries in characteristic zero. Thus `b=0`, and for some `A,B,H,J`, with `A,H≠0`,

```text
y = T+c/T,
x = A(T²+c²/T²)+B = A y²+B−2Ac,
w = H(T³−c³/T³)+J(T−c/T).
```

The slope and intercept of this graph in `y²` are rational. Evaluate at two rational parameters on the original conic with distinct values of `y²`; such parameters exist since the conic is rational and `y` is nonconstant. Writing `a=A, d=B−2Ac` and using the identity of polynomials in `s=y²` gives

```text
s²+8−4(as+d)³ = (s−4c) [H(s−c)+J]².
```

Indeed `(T−c/T)²=y²−4c` and `T³−c³/T³=(T−c/T)(y²−c)`. The square factor contradicts the existence of the given integral triple. This final step, including descent of the multiple root to `ℚ`, is `pole_two_square_factor_excluded` in `PoleTwo.lean`.

## Reproduce the finite checks

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror pole_two_check.cpp -o /tmp/pole_two_check
/tmp/pole_two_check
lake -d .. build PoleOne PellConstantFiber PoleTwo PoleTwoReduction PoleTwoLifting
```
