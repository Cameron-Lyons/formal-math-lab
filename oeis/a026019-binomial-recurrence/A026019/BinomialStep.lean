module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

namespace A026019

/-- The first-order recurrence for the binomial coefficients `choose (3*n) n`. -/
theorem central_step (n : ℕ) :
    2 * (2 * (n : ℚ) + 1) * ((n : ℚ) + 1) *
        ((3 * (n + 1)).choose (n + 1) : ℚ) =
      3 * (3 * (n : ℚ) + 1) * (3 * (n : ℚ) + 2) *
        ((3 * n).choose n : ℚ) := by
  rw [Nat.cast_choose ℚ (by omega : n + 1 ≤ 3 * (n + 1)),
    Nat.cast_choose ℚ (by omega : n ≤ 3 * n)]
  rw [show 3 * (n + 1) = 3 * n + 2 + 1 by omega,
    show 3 * n + 2 + 1 - (n + 1) = 2 * n + 1 + 1 by omega,
    show 3 * n - n = 2 * n by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2n : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h2n1 : 2 * (n : ℚ) + 1 ≠ 0 := by positivity
  have h2n2 : 2 * (n : ℚ) + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring

end A026019
