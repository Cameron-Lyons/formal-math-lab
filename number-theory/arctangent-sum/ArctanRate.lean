module

public import ArctanCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

open Filter Asymptotics

namespace Arxiv.«2607.05739»

private theorem log_nat_tendsto : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Convert the prefix fourth-power bound to a logarithmic power saving for
the inclusive count through N. -/
theorem event_count_isBigO_log_three_quarters {E : Set ℕ}
    (h : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ((labelPrefix E N).card : ℝ)^4 ≤ C*(1+Real.log N)^3) :
    (fun N : ℕ => ((labelPrefix E (N+1)).card : ℝ)) =O[atTop]
      (fun N : ℕ => (Real.log N) ^ (3/4 : ℝ)) := by
  obtain ⟨C, hC⟩ := h
  -- For N large, 1 + log (N + 1) ≤ 3 log N.
  have hlog : ∀ᶠ N : ℕ in atTop, 1 + Real.log (N+1 : ℕ) ≤ 3 * Real.log N := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), log_nat_tendsto.eventually_ge_atTop 1]
      with N hN hlogN
    have hsq : (N+1 : ℝ) ≤ (N : ℝ)^2 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [sq_nonneg ((N : ℝ)-2)]
    have := Real.log_le_log (by positivity) hsq
    rw [Real.log_pow] at this
    norm_num at this
    push_cast
    linarith
  -- Apply the quartic estimate, then take its fourth root.
  have hfour : (fun N : ℕ => ((labelPrefix E (N+1)).card : ℝ)^4) =O[atTop]
      (fun N : ℕ => (Real.log N)^3) := by
    refine isBigO_iff.mpr ⟨27 * max C 0, ?_⟩
    filter_upwards [hlog] with N hN
    have hn := Real.log_natCast_nonneg N
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((labelPrefix E (N+1)).card : ℝ)^4),
      abs_of_nonneg (pow_nonneg hn 3)]
    calc
      _ ≤ C*(1+Real.log (N+1 : ℕ))^3 := hC (N+1) (by omega)
      _ ≤ max C 0 * (3*Real.log N)^3 := by gcongr; exact le_max_left _ _
      _ = _ := by ring
  have hroot := hfour.rpow (by norm_num : 0 ≤ (1/4 : ℝ))
    (Eventually.of_forall fun N => pow_nonneg (Real.log_natCast_nonneg N) 3)
  convert hroot using 2 with N <;>
    rw [← Real.rpow_natCast_mul (by positivity)] <;> norm_num

/-- A fixed nonnegative number of initial events leaves the same rate. -/
theorem event_count_add_isBigO_log_three_quarters {E : Set ℕ} (b : ℕ)
    (h : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ((labelPrefix E N).card : ℝ)^4 ≤ C*(1+Real.log N)^3) :
    (fun N : ℕ => ((labelPrefix E (N+1)).card : ℝ) + b) =O[atTop]
      (fun N : ℕ => (Real.log N) ^ (3/4 : ℝ)) := by
  apply (event_count_isBigO_log_three_quarters h).add
  exact ((isLittleO_const_id_atTop (b : ℝ)).comp_tendsto
    ((tendsto_rpow_atTop (by norm_num : 0 < (3/4 : ℝ))).comp log_nat_tendsto)).isBigO

end Arxiv.«2607.05739»
