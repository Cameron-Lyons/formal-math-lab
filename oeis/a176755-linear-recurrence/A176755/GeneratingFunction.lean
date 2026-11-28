module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

/-! The convolution recurrence gives a polynomial identity for its formal generating function.
All coefficient calculations are finite; no convergence or analytic square root is involved. -/

public section

namespace A176755

open PowerSeries

noncomputable def generatingFunction (a : ℕ → ℤ) : PowerSeries ℤ := PowerSeries.mk a

@[simp]
theorem coeff_generatingFunction (a : ℕ → ℤ) (n : ℕ) :
    coeff n (generatingFunction a) = a n := coeff_mk n a

/-- The exceptional initial values account for the first two coefficients. -/
theorem coeff_quadratic_difference (a : ℕ → ℤ) (h0 : a 0 = 1) (h1 : a 1 = 3)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      a (n + 1) = (∑ p ∈ Finset.range (n + 1), a p * a (n - p)) - 2)
    (n : ℕ) :
    coeff n (generatingFunction a - X * (generatingFunction a)^2) =
      if n = 0 then 1 else if n = 1 then 2 else -2 := by
  cases n with
  | zero => simp [generatingFunction, h0]
  | succ n =>
    rw [map_sub, coeff_succ_X_mul]
    simp only [coeff_generatingFunction, pow_two,
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_generatingFunction]
    cases n with
    | zero => norm_num [h0, h1]
    | succ n =>
      simp only [Nat.succ_ne_zero, Nat.succ.injEq, ↓reduceIte]
      change a (n + 1 + 1) - (∑ p ∈ Finset.range (n + 1 + 1), a p * a (n + 1 - p)) = -2
      rw [hrec (n + 1) (by omega)]
      ring

/-- Multiplication by `1 - X` cancels the constant tail of `F - X F²`. -/
theorem quadratic_of_recurrence (a : ℕ → ℤ) (h0 : a 0 = 1) (h1 : a 1 = 3)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      a (n + 1) = (∑ p ∈ Finset.range (n + 1), a p * a (n - p)) - 2) :
    X * (1-X) * (generatingFunction a)^2 - (1-X) * generatingFunction a +
      1 + X - 4*X^2 = 0 := by
  have h : (1-X) * (generatingFunction a - X * (generatingFunction a)^2) =
      1 + X - 4*X^2 := by
    apply PowerSeries.ext
    intro n
    rw [sub_mul, one_mul]
    cases n with
    | zero => simp [generatingFunction, h0]
    | succ n =>
      simp only [map_sub, coeff_succ_X_mul, coeff_quadratic_difference a h0 h1 hrec]
      rcases n with _ | _ | n
      · norm_num [coeff_X]
      · norm_num [coeff_X]
      · simp [coeff_X_pow, coeff_X, coeff_one]
  linear_combination -h

end A176755
