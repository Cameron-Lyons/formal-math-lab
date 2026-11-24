module

public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section

namespace SmallCubic

/-- A multiple root of a rational cubic is rational, over every field of
characteristic zero. The two formulas correspond to a double and a triple root. -/
theorem rational_multiple_root_of_cubic
    {K : Type*} [Field K] [CharZero K] (a b c d : ℚ) (ha : a ≠ 0) (t : K)
    (hf : (a : K) * t ^ 3 + b * t ^ 2 + c * t + d = 0)
    (hf' : 3 * (a : K) * t ^ 2 + 2 * b * t + c = 0) :
    ∃ r : ℚ, (r : K) = t ∧
      a * r ^ 3 + b * r ^ 2 + c * r + d = 0 ∧
        3 * a * r ^ 2 + 2 * b * r + c = 0 := by
  suffices hr : ∃ r : ℚ, (r : K) = t by
    obtain ⟨r, rfl⟩ := hr
    refine ⟨r, rfl, ?_, ?_⟩
    · apply (Rat.cast_eq_zero (α := K)).mp
      simpa using hf
    · apply (Rat.cast_eq_zero (α := K)).mp
      simpa using hf'
  by_cases h : b ^ 2 - 3 * a * c = 0
  · have hK : (b : K) ^ 2 - 3 * a * c = 0 := by
      simpa using (Rat.cast_eq_zero (α := K)).mpr h
    have hs : (3 * (a : K) * t + b) ^ 2 = 0 := by
      linear_combination 3 * (a : K) * hf' + hK
    have hx := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hs
    refine ⟨-b / (3 * a), ?_⟩
    push_cast
    apply (div_eq_iff ?_).mpr
    · linear_combination -hx
    · exact mul_ne_zero (by norm_num) (Rat.cast_ne_zero.mpr ha)
  · refine ⟨(9 * a * d - b * c) / (2 * (b ^ 2 - 3 * a * c)), ?_⟩
    push_cast
    apply (div_eq_iff ?_).mpr
    · linear_combination 9 * (a : K) * hf - (3 * a * t + b) * hf'
    · exact mul_ne_zero (by norm_num) (by simpa using (Rat.cast_ne_zero (α := K)).mpr h)

end SmallCubic
