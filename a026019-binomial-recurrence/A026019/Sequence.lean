module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity

/-!
# The sequence A026019 and its binomial closed form

We use the complementary lower index `2*n+3` to encode `n-3`.
This makes the second binomial coefficient zero when `n < 3`.
-/

public section

namespace A026019

/-- A026019, with the usual zero convention for negative lower indices. -/
def a (n : ℕ) : ℤ := (Nat.choose (3 * n) n : ℤ) - Nat.choose (3 * n) (2 * n + 3)

/-- The definition agrees with the guarded version of the OEIS formula. -/
theorem a_eq (n : ℕ) :
    a n = (Nat.choose (3 * n) n : ℤ) -
      if 3 ≤ n then (Nat.choose (3 * n) (n - 3) : ℤ) else 0 := by
  unfold a
  split_ifs with h
  · rw [Nat.choose_symm_of_eq_add (show 3 * n = (2 * n + 3) + (n - 3) by omega)]
  · rw [Nat.choose_eq_zero_of_lt (show 3 * n < 2 * n + 3 by omega)]
    simp

/-- A binomial step identity with subtraction in `ℚ`, including `m < k`. -/
private theorem choose_step (m k : ℕ) :
    (Nat.choose m (k + 1) : ℚ) * (k + 1) =
      (Nat.choose m k : ℚ) * ((m : ℚ) - k) := by
  by_cases h : k ≤ m
  · have hc := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_succ_right_eq m k)
    push_cast [Nat.cast_sub h] at hc
    exact hc
  · rw [Nat.choose_eq_zero_of_lt (by omega : m < k + 1),
      Nat.choose_eq_zero_of_lt (by omega : m < k)]
    simp

/-- Clearing the three factors from the binomial ratio gives a cubic prefactor. -/
theorem closed_form_mul (n : ℕ) :
    2 * ((n : ℚ) + 1) * (2 * n + 1) * (2 * n + 3) * (a n : ℚ) =
      (n + 3) * (7 * (n : ℚ)^2 + 6 * n + 2) * (Nat.choose (3 * n) n : ℚ) := by
  have h0 := choose_step (3 * n) (2 * n)
  have h1 := choose_step (3 * n) (2 * n + 1)
  have h2 := choose_step (3 * n) (2 * n + 2)
  have hs : Nat.choose (3 * n) (2 * n) = Nat.choose (3 * n) n :=
    Nat.choose_symm_of_eq_add (by omega)
  rw [hs] at h0
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h0 h1 h2
  norm_num only [show 2 * n + 1 + 1 = 2 * n + 2 by omega,
    show 2 * n + 2 + 1 = 2 * n + 3 by omega] at h1 h2
  unfold a
  push_cast
  linear_combination -((n : ℚ) - 1) * (n - 2) * h0 -
    (2 * (n : ℚ) + 1) * (n - 2) * h1 -
    (2 * (n : ℚ) + 1) * (2 * n + 2) * h2

/-- The rational prefactor relating A026019 to `choose (3*n) n`. -/
theorem closed_form (n : ℕ) :
    (a n : ℚ) =
      (n + 3) * (7 * (n : ℚ)^2 + 6 * n + 2) * (Nat.choose (3 * n) n : ℚ) /
        (2 * ((n : ℚ) + 1) * (2 * n + 1) * (2 * n + 3)) := by
  apply (eq_div_iff (by positivity)).2
  rw [mul_comm]
  exact closed_form_mul n

/-- Initial values, including all indices with a negative lower index in `n-3`. -/
theorem initial_values : a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 15 ∧ a 3 = 83 := by
  norm_num [a, Nat.choose]

end A026019
