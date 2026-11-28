module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! An asymptotic expansion of the complementary angle, centered at `n + 1/2`. -/

@[expose] public section

open Filter Set

namespace Arxiv.«2607.05739»

noncomputable def reciprocalAngle (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, Real.arctan ((k : ℝ)⁻¹)

private noncomputable def profile (h : ℝ) :=
  Real.log h + (5 / 24) / h ^ 2 - (19 / 192) / h ^ 4

/-- The error in replacing one arctangent by a difference of profile values. -/
private noncomputable def localError (x : ℝ) :=
  Real.arctan x - Real.log (1 + x / 2) + Real.log (1 - x / 2) -
    (8 * x ^ 3 * (7 * x ^ 4 + 58 * x ^ 2 - 40)) / (3 * (4 - x ^ 2) ^ 4)

private noncomputable def errorSlope (x : ℝ) :=
  -(x ^ 6 * (71 * x ^ 4 + 2776 * x ^ 2 + 12080)) /
    (3 * (4 - x ^ 2) ^ 5 * (1 + x ^ 2))

set_option maxHeartbeats 2000000 in
private theorem localError_hasDerivAt {x : ℝ} (hx : x ∈ Icc 0 1) :
    HasDerivAt localError (errorSlope x) x := by
  have x2 : x ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hx.1 hx.2 2
  have hp : 1 + x / 2 ≠ 0 := by linarith [hx.1]
  have hm : 1 - x / 2 ≠ 0 := by linarith [hx.2]
  have h4 : 4 - x ^ 2 ≠ 0 := by linarith
  have hden : 3 * (4-x^2)^4 ≠ 0 := by positivity
  have harc := (Real.hasDerivAt_arctan x).differentiableAt
  have hd : DifferentiableAt ℝ localError x := by
    unfold localError; fun_prop (disch := first | assumption | positivity)
  apply hd.hasDerivAt.congr_deriv
  unfold localError errorSlope
  simp (disch := first | assumption | positivity | fun_prop (disch := first | assumption | positivity))
    [deriv_fun_sub, deriv_fun_add, deriv_fun_div, deriv_fun_mul, deriv_fun_pow, deriv.log, Real.deriv_arctan]
  field_simp (disch := first | positivity | nlinarith [hx.1, hx.2, sq_nonneg x])
  ring_nf
  field_simp [show 2 + x ≠ 0 by linarith [hx.1], show 2 - x ≠ 0 by linarith [hx.2]]
  ring

private theorem localError_bound {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    |localError x| ≤ 20000 * x ^ 7 := by
  have slopeBound {y : ℝ} (hy : y ∈ Icc 0 x) : ‖errorSlope y‖ ≤ 20000 * x ^ 6 := by
    have hy₁ := hy.2.trans hx₁
    have h2 : y ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hy.1 hy₁ 2
    have h4 : y ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ hy.1 hy₁ 4
    have hden : 1 ≤ 3 * (4 - y ^ 2) ^ 5 * (1 + y ^ 2) := by
      have h5 : (1 : ℝ) ≤ (4 - y ^ 2) ^ 5 := by
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
          (by linarith : 1 ≤ 4 - y ^ 2) 5
      nlinarith [mul_nonneg (show 0 ≤ (4 - y ^ 2) ^ 5 by linarith) (sq_nonneg y)]
    rw [Real.norm_eq_abs, errorSlope, abs_div, abs_neg, abs_of_nonneg (by positivity),
      abs_of_nonneg (by linarith)]
    calc
      _ ≤ y ^ 6 * (71 * y ^ 4 + 2776 * y ^ 2 + 12080) :=
        div_le_self (by positivity) hden
      _ ≤ x ^ 6 * 20000 :=
        mul_le_mul (pow_le_pow_left₀ hy.1 hy.2 6) (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have bd := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := localError) (a := 0) (b := x)
    (fun y hy => (localError_hasDerivAt ⟨hy.1, hy.2.trans hx₁⟩).hasDerivWithinAt)
    (fun y hy => slopeBound (Ico_subset_Icc_self hy)) x (right_mem_Icc.mpr hx₀)
  simpa [localError, Real.norm_eq_abs, pow_succ, mul_assoc] using bd

set_option maxHeartbeats 2000000 in
private theorem localError_eq {t : ℝ} (ht : 1 ≤ t) :
    localError t⁻¹ = Real.arctan t⁻¹ - (profile (t + 1 / 2) - profile (t - 1 / 2)) := by
  have ht₀ : 0 < t := by linarith
  have hi₁ : t⁻¹ ≤ 1 := (inv_le_one₀ ht₀).mpr ht
  have hip : 0 < t⁻¹ := inv_pos.mpr ht₀
  have h1 : 0 < 1 + t⁻¹ / 2 := by linarith
  have h2 : 0 < 1 - t⁻¹ / 2 := by linarith
  have hp : 0 < t + 1 / 2 := by linarith
  have hm : 0 < t - 1 / 2 := by linarith
  have h4 : 4 - t⁻¹ ^ 2 ≠ 0 := by
    have : t⁻¹ ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hip.le hi₁ 2
    linarith
  have hlp : Real.log (t + 1 / 2) = Real.log t + Real.log (1 + t⁻¹ / 2) := by
    rw [← Real.log_mul ht₀.ne' h1.ne']
    congr 1
    field_simp
  have hlm : Real.log (t - 1 / 2) = Real.log t + Real.log (1 - t⁻¹ / 2) := by
    rw [← Real.log_mul ht₀.ne' h2.ne']
    congr 1
    field_simp
  unfold localError profile
  rw [hlp, hlm]
  suffices hr : 8 * t⁻¹ ^ 3 * (7 * t⁻¹ ^ 4 + 58 * t⁻¹ ^ 2 - 40) /
      (3 * (4 - t⁻¹ ^ 2) ^ 4) =
      (5 / 24) / (t + 1 / 2) ^ 2 - (19 / 192) / (t + 1 / 2) ^ 4 -
      ((5 / 24) / (t - 1 / 2) ^ 2 - (19 / 192) / (t - 1 / 2) ^ 4) by linarith
  field_simp (disch := first | positivity | nlinarith [sq_nonneg (t - 1)])
  ring

private noncomputable def residual (n : ℕ) :=
  reciprocalAngle n - profile ((n : ℝ) + 1 / 2)

private noncomputable def radius (n : ℕ) := 20000 / (n : ℝ) ^ 6

private theorem power_difference {t : ℝ} (ht : 0 < t) :
    (t + 1)⁻¹ ^ 7 ≤ 1 / t ^ 6 - 1 / (t + 1) ^ 6 := by
  have ht₁ : 0 < t + 1 := by linarith
  field_simp [ht, ht₁]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem residual_step (n : ℕ) (hn : 1 ≤ n) :
    |residual (n + 1) - residual n| ≤ radius n - radius (n + 1) := by
  let k := (n : ℝ) + 1
  have hk : 1 ≤ k := by dsimp [k]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hk₀ : 0 < k := by linarith
  have hstep : reciprocalAngle (n + 1) = reciprocalAngle n + Real.arctan k⁻¹ := by
    unfold reciprocalAngle
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), Nat.cast_succ]
  have he : residual (n + 1) - residual n = localError k⁻¹ := by
    rw [localError_eq hk]
    unfold residual
    rw [hstep, Nat.cast_succ]
    rw [show k - 1 / 2 = (n : ℝ) + 1 / 2 by dsimp [k]; ring]
    dsimp only [k]
    ring
  rw [he]
  refine (localError_bound (inv_pos.mpr hk₀).le ((inv_le_one₀ hk₀).mpr hk)).trans ?_
  have hb := mul_le_mul_of_nonneg_left (power_difference (t := (n : ℝ)) (by exact_mod_cast (show 0 < n by omega))) (by norm_num : (0 : ℝ) ≤ 20000)
  simpa only [radius, Nat.cast_succ, k, mul_sub, mul_one_div] using hb

/-- The midpoint expansion of the complementary angle through the fourth-order term. -/
theorem reciprocalAngle_expansion : ∃ C K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
    |reciprocalAngle n - (Real.log ((n : ℝ) + 1 / 2) + C + (5 / 24) / ((n : ℝ) + 1 / 2) ^ 2
        - (19 / 192) / ((n : ℝ) + 1 / 2) ^ 4)| ≤ K / ((n : ℝ) + 1 / 2) ^ 6 := by
  let J (i : ℕ) := Icc (residual (i+1) - radius (i+1)) (residual (i+1) + radius (i+1))
  have nested (i : ℕ) : J (i+1) ⊆ J i := by
    obtain ⟨hl, hu⟩ := abs_le.mp (residual_step (i+1) (by omega))
    exact Icc_subset_Icc (by linarith) (by linarith)
  have inhabited (i : ℕ) : (J i).Nonempty :=
    nonempty_Icc.mpr (by linarith [show 0 ≤ radius (i+1) by unfold radius; positivity])
  obtain ⟨C, hC⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    J nested inhabited isCompact_Icc (fun _ => isClosed_Icc)
  refine ⟨C, 20000 * 2 ^ 6, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hres : |residual n - C| ≤ radius n := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    obtain ⟨h₁,h₂⟩ := Set.mem_iInter.mp hC i
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hid : reciprocalAngle n - (Real.log ((n : ℝ) + 1 / 2) + C +
      (5 / 24) / ((n : ℝ) + 1 / 2) ^ 2 - (19 / 192) / ((n : ℝ) + 1 / 2) ^ 4) =
      residual n - C := by unfold residual profile; ring
  rw [hid]
  refine hres.trans ?_
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow := pow_le_pow_left₀ (show 0 ≤ (n : ℝ) + 1 / 2 by positivity)
    (show (n : ℝ) + 1 / 2 ≤ 2 * n by linarith) 6
  rw [radius, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [mul_pow] at hpow
  linarith

end Arxiv.«2607.05739»
