module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Tactic.LinearCombination

public section

namespace A176755

open PowerSeries

private theorem coeff_euler (F : PowerSeries ℤ) (n : ℕ) :
    coeff n (X * derivative F) = (n : ℤ) * coeff n F := by
  cases n <;> simp [coeff_succ_X_mul, coeff_derivative, mul_comm]

/-- Comparing coefficients in the first-order differential equation yields Mathar's
five-term recurrence. -/
theorem coefficients_of_differential (F : PowerSeries ℤ)
    (hd : X * (1 - 6 * X + X ^ 2 + 20 * X ^ 3 - 16 * X ^ 4) * derivative F +
      (1 - 4 * X + 5 * X ^ 2 - 6 * X ^ 3) * F =
      1 + 2 * X - 13 * X ^ 2 + 8 * X ^ 3)
    (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℤ) + 1) * coeff n F +
      2 * (1 - 3 * (n : ℤ)) * coeff (n - 1) F +
      ((n : ℤ) + 3) * coeff (n - 2) F +
      2 * (10 * (n : ℤ) - 33) * coeff (n - 3) F +
      16 * (4 - (n : ℤ)) * coeff (n - 4) F = 0 := by
  let E : PowerSeries ℤ := X * derivative F
  have he : E - 6 * (X ^ 1 * E) + X ^ 2 * E + 20 * (X ^ 3 * E) -
      16 * (X ^ 4 * E) + F - 4 * (X ^ 1 * F) + 5 * (X ^ 2 * F) -
      6 * (X ^ 3 * F) = 1 + 2 * X - 13 * X ^ 2 + 8 * X ^ 3 := by
    convert hd using 1
    dsimp [E]
    ring
  have hc := congrArg (coeff n) he
  simp (disch := omega) only [map_add, map_sub, coeff_ofNat_mul,
    coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_one,
    ite_eq_left, ite_eq_right, E, coeff_euler,
    Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one] at hc
  linear_combination hc

end A176755
