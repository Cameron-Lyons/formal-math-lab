module

public import ArctanPhase
public import ArctanPole
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Assigning a distinct multiple of π/2 to each integer event. -/

@[expose] public section

namespace Arxiv.«2607.05739»

def integerEvents : Set ℕ := {n | 5 ≤ n ∧ IsIntegerValue n}

noncomputable def poleLabel (n : ℕ) : ℕ := by
  classical
  exact if h : n ∈ integerEvents then (pole_label h.1 h.2).choose else 0

theorem event_label_error {n : ℕ} (h : n ∈ integerEvents) :
    |reciprocalAngle n - (poleLabel n : ℝ) * (Real.pi / 2)| < 1 / (n : ℝ) ^ 10 := by
  simpa only [poleLabel, dite_eq_left h, reciprocalAngle] using (pole_label h.1 h.2).choose_spec

private theorem half_le_arctan {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    x / 2 ≤ Real.arctan x := by
  have h₂ : x ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hx₀ hx₁ 2
  have hs : Real.sqrt (1 + x ^ 2) ≤ 2 := (Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩)
  have := Real.sin_le (Real.arctan_nonneg.mpr hx₀)
  rw [Real.sin_arctan] at this
  exact (div_le_div_of_nonneg_left hx₀ (by positivity) hs).trans this

/-- A single added summand separates the phases by more than the sum of
the two possible errors in approximating a pole. -/
private theorem reciprocalAngle_gap {n m : ℕ} (hn : 5 ≤ n) (hnm : n < m) :
    2/(n : ℝ)^10 < reciprocalAngle m - reciprocalAngle n := by
  have hn₅ : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hpow : (n : ℝ)^2 ≤ (n : ℝ)^10 := pow_le_pow_right₀ (by linarith) (by decide)
  have hstep : reciprocalAngle (n+1) ≤ reciprocalAngle m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hnm)
      (fun k _ _ => Real.arctan_nonneg.mpr (by positivity))
  calc
    2/(n : ℝ)^10 < ((n : ℝ)+1)⁻¹ / 2 := by
      rw [inv_eq_one_div, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((n : ℝ)-5)]
    _ ≤ Real.arctan (((n : ℝ)+1)⁻¹) := half_le_arctan (by positivity)
      ((inv_le_one₀ (by positivity)).mpr (by linarith))
    _ = reciprocalAngle (n+1) - reciprocalAngle n := by
      simp [reciprocalAngle, Finset.sum_Icc_succ_top]
    _ ≤ _ := sub_le_sub_right hstep _

theorem event_labels_injective : Set.InjOn poleLabel integerEvents := by
  apply StrictMonoOn.injOn
  intro n hn m hm hnm
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (by have := hn.1; omega : 0 < n)
  have herrors : 1 / (m : ℝ)^10 ≤ 1 / (n : ℝ)^10 := by gcongr
  have hlo := (abs_lt.mp (event_label_error hn)).1
  have hhi := (abs_lt.mp (event_label_error hm)).2
  have hgap := reciprocalAngle_gap hn.1 hnm
  rw [show 2/(n : ℝ)^10 = 1/(n : ℝ)^10 + 1/(n : ℝ)^10 by ring] at hgap
  have hlt : (poleLabel n : ℝ)*(Real.pi/2) < (poleLabel m : ℝ)*(Real.pi/2) := by
    linarith only [hgap, hlo, hhi, herrors]
  exact_mod_cast (mul_lt_mul_iff_left₀ (by positivity : 0 < Real.pi/2)).mp hlt

theorem event_label_le {n : ℕ} (h : n ∈ integerEvents) :
    (poleLabel n : ℝ) ≤ 2 * (1 + Real.log n) := by
  have ha : reciprocalAngle n ≤ 1 + Real.log n := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 n, ((k : ℝ)⁻¹) :=
        Finset.sum_le_sum fun k _ => Real.arctan_le_self (by positivity)
      _ = (harmonic n : ℝ) := by simp [harmonic_eq_sum_Icc]
      _ ≤ _ := harmonic_le_one_add_log n
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from (by omega : 1 ≤ 5).trans h.1)
  have hs := (abs_lt.mp (event_label_error h)).1
  have he : 1 / (n : ℝ)^10 ≤ 1 := by
    apply (div_le_one (pow_pos (by linarith) 10)).mpr
    exact one_le_pow₀ hn
  have hp : (poleLabel n : ℝ) ≤ (poleLabel n : ℝ) * (Real.pi / 2) :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith [Real.pi_gt_three])
  linarith [Real.log_natCast_nonneg n]

end Arxiv.«2607.05739»
