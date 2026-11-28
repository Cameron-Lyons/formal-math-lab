module

public import ArctanAngles
public import ArctanPolynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

public section

namespace Arxiv.«2607.05739»

/-- At an integer event the reciprocal-arctangent sum is close to an integer
multiple of π/2. Here the error can be taken strictly below n⁻¹⁰. -/
theorem pole_label {n : ℕ} (hn : 5 ≤ n) (hv : IsIntegerValue n) :
    ∃ j : ℕ, |(∑ k ∈ Finset.Icc 1 n, Real.arctan ((k : ℝ)⁻¹)) -
      (j : ℝ) * (Real.pi / 2)| < 1 / (n : ℝ)^10 := by
  obtain ⟨m, hm⟩ := hv
  have hbig := index_pow_ten_lt_natAbs hn hm
  have hmpos : (n : ℝ)^10 < |(m : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    exact_mod_cast hbig
  have hm0 : (m : ℝ) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hmpos
    exact (pow_nonneg (Nat.cast_nonneg n) 10).not_gt hmpos
  let t := ∑ k ∈ Finset.Icc 1 n, Real.arctan (k : ℝ)
  have ht : Real.tan t = (m : ℝ) := tan_eq_int_iff.mpr hm
  have hc : Real.cos (t + Real.arctan (m : ℝ)⁻¹) = 0 := by
    have hs : Real.sin t = (m : ℝ) * Real.cos t := by
      rw [← ht, Real.tan_mul_cos]
      exact cos_sum_arctan_ne_zero n
    have hz : Real.sin (Real.arctan (m : ℝ)⁻¹) =
        (m : ℝ)⁻¹ * Real.cos (Real.arctan (m : ℝ)⁻¹) := by
      rw [← Real.tan_mul_cos (Real.cos_arctan_pos _).ne', Real.tan_arctan]
    rw [Real.cos_add, hs, hz]
    field_simp
    ring
  obtain ⟨z, hz⟩ := Real.cos_eq_zero_iff.mp hc
  let j : ℤ := n - (2*z+1)
  let a := ∑ k ∈ Finset.Icc 1 n, Real.arctan ((k : ℝ)⁻¹)
  have hsum : t + a = n * (Real.pi / 2) := by
    unfold t a
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _k ∈ Finset.Icc 1 n, (Real.pi / 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Real.arctan_inv_of_pos (by exact_mod_cast (Finset.mem_Icc.mp hk).1 : 0 < (k : ℝ))]
        ring
      _ = _ := by simp
  have herr : a - (j : ℝ) * (Real.pi / 2) = Real.arctan (m : ℝ)⁻¹ := by
    dsimp [j]
    push_cast
    linarith
  have hsmall : |a - (j : ℝ) * (Real.pi / 2)| < 1 / (n : ℝ)^10 := by
    rw [herr]
    apply Real.abs_arctan_le_abs.trans_lt
    rw [abs_inv, ← one_div]
    exact one_div_lt_one_div_of_lt (by positivity) hmpos
  -- The reciprocal-angle sum is nonnegative, so replacing j by |j| can only shrink the error.
  have ha : 0 ≤ a := Finset.sum_nonneg fun k _ => Real.arctan_nonneg.mpr (by positivity)
  refine ⟨j.natAbs, lt_of_le_of_lt ?_ hsmall⟩
  simpa only [abs_of_nonneg ha, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.pi/2),
    ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast] using
    abs_abs_sub_abs_le_abs_sub a ((j : ℝ) * (Real.pi/2))

end Arxiv.«2607.05739»
