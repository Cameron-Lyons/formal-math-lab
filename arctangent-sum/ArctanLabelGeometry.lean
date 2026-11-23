module

public import ArctanDeterminant
public import ArctanCounting

public section

open Finset
open scoped Classical

namespace Arxiv.«2607.05739»

/-- Possible labels at which an integer lies in the inverse-phase enclosure. -/
@[expose] def modelLabels (c t H : ℝ) : Set ℕ := {j | ∃ u : ℤ, InversePhaseApprox H (c*t^j) u}

/-- Read the four integer approximations in one translated parallelogram and
apply the determinant estimate at its starting scale. -/
private theorem model_det_on_block {c t H : ℝ} {J i a b : ℕ} (hc : 0 ≤ c) (ht : 1 ≤ t)
    (hH : 0 ≤ H) (hy : 1 ≤ c*t^J)
    (hi : i ∈ labelPairs (labelPairs (labelDyad (modelLabels c t H) J) a) b) :
    c*t^J ≤ c*t^i ∧ a+b ≤ J ∧
      ∃ d : ℤ, |(d : ℝ) - detConstant (t^a) (t^b) -
        detCorrection (t^a) (t^b)/(c*t^i)^2| ≤ detErrorBound H*(t^a*t^b)/(c*t^i)^4 := by
  simp only [labelPairs, labelDyad, mem_filter] at hi
  obtain ⟨⟨h₀, h₁⟩, h₂, h₃⟩ := hi
  obtain ⟨hstart, u, hu⟩ := h₀
  obtain ⟨_, v, hv⟩ := h₁
  obtain ⟨_, w, hw⟩ := h₂
  obtain ⟨hend, x, hx⟩ := h₃
  have hlo := (mem_Ico.mp hstart).1
  have hhi := (mem_Ico.mp hend).2
  have hscale := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hlo) hc
  refine ⟨hscale, by omega, u*x-v*w, ?_⟩
  push_cast
  apply determinant_approx hH (hy.trans hscale) (one_le_pow₀ ht) (one_le_pow₀ ht) hu
  · simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hv
  · simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hw
  · simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hx

/-- On each sufficiently late dyadic block, two translates of the same label
parallelogram would give distinct integers at distance less than one. -/
theorem modelLabels_dyadic {c t H : ℝ} (hc : 0 < c) (ht : 2 ≤ t) (hH : 0 ≤ H) :
    ∃ J₀ : ℕ, ∀ J ≥ J₀, (((Ico J (2*J)).filter (· ∈ modelLabels c t H)).card)^4 ≤
      208*(J+1)^3 := by
  let C := detErrorBound H
  have hC : 0 ≤ C := detErrorBound_nonneg hH
  have ht1 : 1 ≤ t := by linarith
  obtain ⟨J₀,hJ₀⟩ := pow_unbounded_of_one_lt (max ((256*C+1)/c) (2/c^2)) (by linarith : 1 < t)
  refine ⟨J₀, fun J hJ => ?_⟩
  have hJpow := hJ₀.trans_le (pow_le_pow_right₀ ht1 hJ)
  have hbase : 256*C+1 < c*t^J := by
    have := (div_lt_iff₀ hc).mp ((le_max_left _ _).trans_lt hJpow)
    linarith
  have hbase' : 2 < c^2*t^J := by
    have := (div_lt_iff₀ (sq_pos_of_pos hc)).mp ((le_max_right _ _).trans_lt hJpow)
    linarith
  have hyJ : 1 ≤ c*t^J := by linarith
  apply labelDyad_card_fourth
  intro a b ha hb
  let starts := labelPairs (labelPairs (labelDyad (modelLabels c t H) J) a) b
  have hpow {k : ℕ} (hk : 0 < k) : 2 ≤ t^k :=
    ht.trans (by simpa using (pow_le_pow_right₀ ht1 (show 1 ≤ k by omega)))
  have distinct_impossible {i j : ℕ} (hij : i < j) (hi : i ∈ starts) (hj : j ∈ starts) : False := by
    obtain ⟨hiScale, hgap, d, hd⟩ := model_det_on_block hc.le ht1 hH hyJ hi
    obtain ⟨_, _, d', hd'⟩ := model_det_on_block hc.le ht1 hH hyJ hj
    have yi := hyJ.trans hiScale
    have hsep : 2*(c*t^i) ≤ c*t^j := calc
      _ ≤ t*(c*t^i) := mul_le_mul_of_nonneg_right ht (by positivity)
      _ = c*t^(i+1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 hij) hc.le
    have hqr : t^a*t^b ≤ t^J := by rw [← pow_add]; exact pow_le_pow_right₀ ht1 hgap
    have hsize : 2*(t^a*t^b) < (c*t^i)^2 := calc
      _ ≤ 2*t^J := by linarith
      _ < (c^2*t^J)*t^J := mul_lt_mul_of_pos_right hbase' (by positivity)
      _ = (c*t^J)^2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hiScale 2
    apply translated_determinants_impossible hC yi hsep (hpow ha) (hpow hb) _ hsize hd hd'
    nlinarith [sq_nonneg (c*t^i-1)]

  apply card_le_one_iff.mpr
  intro i j hi hj
  exact le_antisymm (le_of_not_gt (fun h => distinct_impossible h hj hi))
    (le_of_not_gt (fun h => distinct_impossible h hi hj))

end Arxiv.«2607.05739»
