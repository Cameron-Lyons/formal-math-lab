module

public import ArctanNonzero
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

public section

namespace Arxiv.«2607.05739»

private noncomputable def angle (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, Real.arctan k

/-- The unit vector at the summed angle is a positive multiple of the
integer vector obtained from the Gaussian product. -/
private theorem exists_scale (n : ℕ) : ∃ t : ℝ, 0 < t ∧
    Real.cos (angle n) = t * (coords n).1 ∧ Real.sin (angle n) = t * (coords n).2 := by
  induction n with
  | zero => exact ⟨1, by norm_num, by simp [angle, coords], by simp [angle, coords]⟩
  | succ n ih =>
      obtain ⟨t, ht, hc, hs⟩ := ih
      let k := ((n + 1 : ℕ) : ℝ)
      have hpos := Real.cos_arctan_pos k
      have hsin : Real.sin (Real.arctan k) = k * Real.cos (Real.arctan k) := by
        apply (div_eq_iff hpos.ne').mp
        rw [← Real.tan_eq_sin_div_cos, Real.tan_arctan]
      have ha : angle (n + 1) = angle n + Real.arctan k :=
        Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)) _
      refine ⟨t * Real.cos (Real.arctan k), mul_pos ht hpos, ?_, ?_⟩
      · rw [ha, Real.cos_add, hc, hs, hsin]
        simp only [coords, Int.cast_sub, Int.cast_mul, Int.cast_natCast, k]
        ring
      · rw [ha, Real.sin_add, hc, hs, hsin]
        simp only [coords, Int.cast_add, Int.cast_mul, Int.cast_natCast, k]
        ring

/-- The trigonometric sum never encounters a pole of the tangent. -/
theorem cos_sum_arctan_ne_zero (n : ℕ) :
    Real.cos (∑ k ∈ Finset.Icc 1 n, Real.arctan k) ≠ 0 := by
  obtain ⟨t, ht, hc, _⟩ := exists_scale n
  change Real.cos (angle n) ≠ 0
  rw [hc, coords_eq]
  exact mul_ne_zero ht.ne' (by exact_mod_cast A_ne_zero n)

theorem tan_sum_arctan_eq (n : ℕ) :
    Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) = (B n : ℝ) / (A n : ℝ) := by
  obtain ⟨t, ht, hc, hs⟩ := exists_scale n
  change Real.tan (angle n) = _
  rw [Real.tan_eq_sin_div_cos, hs, hc, coords_eq, mul_div_mul_left _ _ ht.ne']

/-- Taking an integer value is exactly the Gaussian-coordinate equation B = A m. -/
theorem tan_eq_int_iff {n : ℕ} {m : ℤ} :
    Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) = (m : ℝ) ↔ B n = A n * m := by
  rw [tan_sum_arctan_eq, div_eq_iff (show (A n : ℝ) ≠ 0 by exact_mod_cast A_ne_zero n),
    mul_comm]
  exact_mod_cast Iff.rfl

theorem isIntegerValue_iff_tan (n : ℕ) :
    IsIntegerValue n ↔ ∃ m : ℤ, Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) = (m : ℝ) :=
  exists_congr fun _ => tan_eq_int_iff.symm

end Arxiv.«2607.05739»
