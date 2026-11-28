module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Tactic.LinearCombination

public section

namespace A176755

open PowerSeries

/-- Eliminate the quadratic generating-function equation and its derivative. -/
theorem differential_of_quadratic (F : PowerSeries ℤ)
    (h : X * (1-X) * F^2 - (1-X)*F + 1 + X - 4*X^2 = 0) :
    X*(1-6*X+X^2+20*X^3-16*X^4)*PowerSeries.derivative F +
      (1-4*X+5*X^2-6*X^3)*F = 1+2*X-13*X^2+8*X^3 := by
  have hd := congrArg (PowerSeries.derivative (R := ℤ)) h
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.map_one_eq_zero,
    map_zero, derivative_X, derivative_pow, Nat.reduceSub, pow_one, smul_eq_mul,
    show PowerSeries.derivative (4 : PowerSeries ℤ) = 0 from derivative_C] at hd
  have hs : (1 - 2*X*F : PowerSeries ℤ) ≠ 0 := by
    intro he
    simpa using congrArg (PowerSeries.constantCoeff (R := ℤ)) he
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp ?_).resolve_left hs
  -- This polynomial combination equals the differential-equation residual times `1 - 2*X*F`.
  linear_combination (-1-4*X^2+32*X^3)*h -
    X*(1-5*X-4*X^2+16*X^3)*hd

end A176755
