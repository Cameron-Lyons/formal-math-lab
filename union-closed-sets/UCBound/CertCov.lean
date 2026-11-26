module

public import UCBound.CertCovChk
public import UCBound.SubsetAvg
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

/-!
# Certified Covariance Inequality (Proposition S4 / `LocalInequalities.hCov`)

Proves for all finite probability distributions `(w, Y)` with `Y_i ∈ [0, 1]` and mean `a = ∑ w_i Y_i`:
  `∑ w_i (Y_i - a) h(Y_i) ≤ (39/100) (h(a) - ∑ w_i h(Y_i)) + (13/25) ∑ w_i R_fun(Y_i)`.

Split into three regimes matching `cov_independent.cpp` and `cov_exterior.cpp`:
1. `a ∈ (0, 1/12)`: `g(x) = (x + 39/100 - a) h(x)` is concave on `[0, 1]` (`treeCovLow` + analytic tail),
   then Jensen's inequality gives `∑ w_i g(Y_i) ≤ g(a) = (39/100) h(a)`.
2. `a ∈ [1/12, 2/3]`: supporting-affine pointwise bound `Fa(a, x) ≥ 0` (`treeCovInt` + analytic tails).
3. `a ∈ (2/3, 1)`: relative-entropy pointwise bound `(39/100) KL(x || a) - (a - x)(h(a) - h(x)) ≥ 0`
   (automatic for `x ≥ 1 - a`, analytic for `a ≥ 15/16` and `x ≤ 2^{-12}`, `treeCovHi` on the rest).
-/

namespace UCBound.Cert2D

open scoped BigOperators
open UCBound UCBound.Iv UCBound.Cert UCBound.FastIv

/-! ### Helper Real Functions, Soundness, and Certified Elementary Bounds -/

noncomputable def Fa_fun (a x : ℝ) : ℝ :=
  (39 / 100 : ℝ) * x * (h a / a) + (7 / 10000 : ℝ) * (a - x)
  - (x + 39 / 100 - a) * h x + (13 / 25 : ℝ) * R_fun x

noncomputable def Fa_da (a x : ℝ) : ℝ :=
  (39 / 100 : ℝ) * x * (Real.log (1 - a) / a ^ 2) + 7 / 10000 + h x

noncomputable def Fa_dx (a x : ℝ) : ℝ :=
  (39 / 100 : ℝ) * (h a / a) - 7 / 10000 - (h x + (x + 39 / 100 - a) * hp x)
  + (13 / 25 : ℝ) * RP x

noncomputable def KL_fun (x a : ℝ) : ℝ :=
  -h x - x * Real.log a - (1 - x) * Real.log (1 - a)

noncomputable def Ghi_fun (a x : ℝ) : ℝ :=
  (39 / 100 : ℝ) * KL_fun x a - (a - x) * (h a - h x)

noncomputable def Ghi_da (a x : ℝ) : ℝ :=
  (39 / 100 : ℝ) * ((a - x) / (a * (1 - a))) - (h a - h x) - (a - x) * hp a

noncomputable def Ghi_dx (a x : ℝ) : ℝ :=
  (39 / 100 : ℝ) * (hp a - hp x) + (h a - h x) + (a - x) * hp x

private lemma mem_kapIv : mem kapIv (39 / 100 : ℝ) := by unfold kapIv; simpa using mem_ofRat (p := 39) (q := 100) (by norm_num)
private lemma mem_CcovIv : mem CcovIv (13 / 25 : ℝ) := by unfold CcovIv; simpa using mem_ofRat (p := 13) (q := 25) (by norm_num)
private lemma mem_deltaIv : mem deltaIv (7 / 10000 : ℝ) := by unfold deltaIv; simpa using mem_ofRat (p := 7) (q := 10000) (by norm_num)
private lemma mem_r1_12Iv : mem r1_12Iv (1 / 12 : ℝ) := by unfold r1_12Iv; simpa using mem_ofRat (p := 1) (q := 12) (by norm_num)

private lemma hasDerivAt_h_div_id {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun t => h t / t) (Real.log (1 - a) / a ^ 2) a := by
  have hd := (hasDerivAt_h ha0 ha1).div (hasDerivAt_id' a) (ne_of_gt ha0)
  refine hd.congr_deriv ?_
  have h1 : hp a * a - h a * 1 = Real.log (1 - a) := by
    unfold hp h; rw [Real.log_div (by linarith) (ne_of_gt ha0)]; ring
  rw [h1]

private lemma h_div_id_antitone : AntitoneOn (fun t => h t / t) (Set.Ioc (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
  · exact (continuousOn_h.mono Set.Ioc_subset_Icc_self).div continuousOn_id (fun t ht => ne_of_gt ht.1)
  · intro t ht; rw [interior_Ioc] at ht
    exact (hasDerivAt_h_div_id ht.1 ht.2).differentiableAt.differentiableWithinAt
  · intro t ht; rw [interior_Ioc] at ht
    rw [(hasDerivAt_h_div_id ht.1 ht.2).deriv]
    have hlog : Real.log (1 - t) ≤ 0 := Real.log_nonpos (by linarith [ht.2]) (by linarith [ht.1])
    exact div_nonpos_of_nonpos_of_nonneg hlog (sq_nonneg t)

private lemma KL_eq_tangent {x a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    KL_fun x a = h a + (x - a) * hp a - h x := by
  unfold KL_fun h hp; rw [Real.log_div (by linarith) (ne_of_gt ha0)]; ring

private lemma KL_nonneg {x a : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ha0 : 0 < a) (ha1 : a < 1) :
    0 ≤ KL_fun x a := by
  rw [KL_eq_tangent ha0 ha1]
  rcases lt_trichotomy x a with hlt | rfl | hgt
  · have hcont : ContinuousOn h (Set.Icc x a) := continuousOn_h.mono (Set.Icc_subset_Icc hx0 (le_of_lt ha1))
    have hdiff : ∀ t ∈ Set.Ioo x a, HasDerivAt h (hp t) t := fun t ht =>
      hasDerivAt_h (lt_of_le_of_lt hx0 ht.1) (lt_trans ht.2 ha1)
    obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope h hp hlt hcont hdiff
    have hanti : AntitoneOn hp (Set.Ioo (0 : ℝ) 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
      · intro t ht; exact (hasDerivAt_hp ht.1 ht.2).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Ioo] at ht; exact (hasDerivAt_hp ht.1 ht.2).differentiableAt.differentiableWithinAt
      · intro t ht; rw [interior_Ioo] at ht
        rw [(hasDerivAt_hp ht.1 ht.2).deriv]
        have : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
        linarith [one_div_pos.mpr this]
    have hge : hp a ≤ hp c := hanti ⟨lt_of_le_of_lt hx0 hc.1, lt_trans hc.2 ha1⟩ ⟨ha0, ha1⟩ (le_of_lt hc.2)
    have hax : 0 < a - x := sub_pos.mpr hlt
    have heq : h a - h x = hp c * (a - x) := by rw [hmv]; field_simp [ne_of_gt hax]
    nlinarith
  · ring_nf; linarith
  · have hcont : ContinuousOn h (Set.Icc a x) := continuousOn_h.mono (Set.Icc_subset_Icc (le_of_lt ha0) hx1)
    have hdiff : ∀ t ∈ Set.Ioo a x, HasDerivAt h (hp t) t := fun t ht =>
      hasDerivAt_h (lt_trans ha0 ht.1) (lt_of_lt_of_le ht.2 hx1)
    obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope h hp hgt hcont hdiff
    have hanti : AntitoneOn hp (Set.Ioo (0 : ℝ) 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
      · intro t ht; exact (hasDerivAt_hp ht.1 ht.2).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Ioo] at ht; exact (hasDerivAt_hp ht.1 ht.2).differentiableAt.differentiableWithinAt
      · intro t ht; rw [interior_Ioo] at ht
        rw [(hasDerivAt_hp ht.1 ht.2).deriv]
        have : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
        linarith [one_div_pos.mpr this]
    have hle : hp c ≤ hp a := hanti ⟨ha0, ha1⟩ ⟨lt_trans ha0 hc.1, lt_of_lt_of_le hc.2 hx1⟩ (le_of_lt hc.1)
    have hxa : 0 < x - a := sub_pos.mpr hgt
    have heq : h x - h a = hp c * (x - a) := by rw [hmv]; field_simp [ne_of_gt hxa]
    nlinarith

private lemma h_mono_left : MonotoneOn h (Set.Icc (0 : ℝ) (1 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
  · exact continuousOn_h.mono (Set.Icc_subset_Icc le_rfl (by norm_num))
  · intro x hx; rw [interior_Icc] at hx
    exact (hasDerivAt_h hx.1 (by linarith [hx.2])).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Icc] at hx
    rw [(hasDerivAt_h hx.1 (by linarith [hx.2])).deriv]
    unfold hp
    exact Real.log_nonneg (by rw [one_le_div hx.1]; linarith [hx.2])

private lemma h_anti_right : AntitoneOn h (Set.Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [← h_symm x, ← h_symm y]
  exact h_mono_left ⟨by linarith [hy.2], by linarith [hy.1]⟩ ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)

private lemma L_lt_694 : L < (694 / 1000 : ℝ) := by
  have ht : mem (ofRat 694 1000) (694 / 1000 : ℝ) := by convert mem_ofRat (p := 694) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo mem_LN2 ht (by decide)

private lemma L_gt_693 : (693 / 1000 : ℝ) < L := by
  have ht : mem (ofRat 693 1000) (693 / 1000 : ℝ) := by convert mem_ofRat (p := 693) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo ht mem_LN2 (by decide)

private lemma h_inv65536_lt : h (1 / 65536 : ℝ) < (185 / 1000000 : ℝ) := by
  have hx : mem (pt cx1) (1 / 65536 : ℝ) := by
    have : ((cx1 : ℝ) / SCALE) = 1 / 65536 := by unfold cx1 SCALE; norm_num
    rw [← this]; exact mem_pt cx1
  have ht : mem (ofRat 185 1000000) (185 / 1000000 : ℝ) := by convert mem_ofRat (p := 185) (q := 1000000) (by norm_num)
  exact lt_of_hi_lt_lo (mem_fastH hx (by norm_num) (by norm_num)) ht (by decide)

private lemma h_two_thirds_gt : (636 / 1000 : ℝ) < h (2 / 3 : ℝ) := by
  have hx : mem (ofRat 2 3) (2 / 3 : ℝ) := by convert mem_ofRat (p := 2) (q := 3) (by norm_num)
  have ht : mem (ofRat 636 1000) (636 / 1000 : ℝ) := by convert mem_ofRat (p := 636) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo ht (mem_fastH hx (by norm_num) (by norm_num)) (by decide)

private lemma h_two_thirds_lt : h (2 / 3 : ℝ) < (637 / 1000 : ℝ) := by
  have hx : mem (ofRat 2 3) (2 / 3 : ℝ) := by convert mem_ofRat (p := 2) (q := 3) (by norm_num)
  have ht : mem (ofRat 637 1000) (637 / 1000 : ℝ) := by convert mem_ofRat (p := 637) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo (mem_fastH hx (by norm_num) (by norm_num)) ht (by decide)

private lemma h_255_256_lt : h (255 / 256 : ℝ) < (26 / 1000 : ℝ) := by
  have hx : mem (pt cx2) (255 / 256 : ℝ) := by
    have : ((cx2 : ℝ) / SCALE) = 255 / 256 := by unfold cx2 SCALE; norm_num
    rw [← this]; exact mem_pt cx2
  have ht : mem (ofRat 26 1000) (26 / 1000 : ℝ) := by convert mem_ofRat (p := 26) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo (mem_fastH hx (by norm_num) (by norm_num)) ht (by decide)

private lemma h_1_16_lt : h (1 / 16 : ℝ) < (234 / 1000 : ℝ) := by
  have hx : mem (ofRat 1 16) (1 / 16 : ℝ) := by simpa using mem_ofRat (p := 1) (q := 16) (by norm_num)
  have ht : mem (ofRat 234 1000) (234 / 1000 : ℝ) := by convert mem_ofRat (p := 234) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo (mem_fastH hx (by norm_num) (by norm_num)) ht (by decide)

private lemma log_3_gt : (10985 / 10000 : ℝ) < Real.log 3 := by
  have hx : mem (ofInt 3) (3 : ℝ) := by simpa using mem_ofInt 3
  have ht : mem (ofRat 10985 10000) (10985 / 10000 : ℝ) := by convert mem_ofRat (p := 10985) (q := 10000) (by norm_num)
  exact lt_of_hi_lt_lo ht (mem_fastLog hx (by decide)) (by decide)

private lemma log_15_lt : Real.log 15 < (271 / 100 : ℝ) := by
  have hx : mem (ofInt 15) (15 : ℝ) := by simpa using mem_ofInt 15
  have ht : mem (ofRat 271 100) (271 / 100 : ℝ) := by convert mem_ofRat (p := 271) (q := 100) (by norm_num)
  exact lt_of_hi_lt_lo (mem_fastLog hx (by decide)) ht (by decide)

/-! ### Regime 1: Low Mean `a ∈ (0, 1/12)` (Concavity + Jensen) -/

private lemma cov_low_mean {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 12) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => (x + 39 / 100 - a) * h x) := by
  set g : ℝ → ℝ := fun x => (x + 39 / 100 - a) * h x
  set g' : ℝ → ℝ := fun x => h x + (x + 39 / 100 - a) * hp x
  have hdg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (g' x) x := fun x hx => by
    have h1 : HasDerivAt (fun t => t + 39 / 100 - a) 1 x := by
      simpa using ((hasDerivAt_id' x).add_const (39 / 100 : ℝ)).sub_const a
    have h2 := hasDerivAt_h hx.1 hx.2
    exact (h1.fun_mul h2).congr_deriv (by simp only [g']; ring)
  have hdg' : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g' (2 * hp x + (x + 39 / 100 - a) * hpp x) x := fun x hx => by
    have h1 := hasDerivAt_h hx.1 hx.2
    have h2 : HasDerivAt (fun t => t + 39 / 100 - a) 1 x := by
      simpa using ((hasDerivAt_id' x).add_const (39 / 100 : ℝ)).sub_const a
    have h3 := hasDerivAt_hp hx.1 hx.2
    exact (h1.fun_add (h2.fun_mul h3)).congr_deriv (by unfold hpp; ring)
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    ((continuous_id.add continuous_const |>.sub continuous_const).continuousOn).mul continuousOn_h
  apply concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hg_cont
  · intro x hx; rw [interior_Icc] at hx
    exact (hdg x hx).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Icc] at hx
    have hdeq : deriv g =ᶠ[nhds x] g' := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy; exact (hdg y hy).deriv
    exact ((hdg' x hx).congr_of_eventuallyEq hdeq).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Icc] at hx
    have hdeq : deriv g =ᶠ[nhds x] g' := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy; exact (hdg y hy).deriv
    have h2 := ((hdg' x hx).congr_of_eventuallyEq hdeq).deriv
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rw [h2]
    have hx1m : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
    have hnum : 2 * x * (1 - x) * hp x - x ≤ 39 / 100 - a := by
      by_cases hhalf : x ≤ 1 / 2
      · by_cases hlo : x ≤ (cLowLo : ℝ) / SCALE
        · have hx20 : x ≤ 1 / 1048576 := by
            have : (cLowLo : ℝ) / SCALE = 1 / 1048576 := by unfold cLowLo SCALE; norm_num
            linarith
          have hhp : hp x ≤ -Real.log x := by
            unfold hp; rw [Real.log_div (by linarith [hx.2]) (ne_of_gt hx.1)]
            have := Real.log_nonpos (show (0 : ℝ) ≤ 1 - x by linarith [hx.2]) (show 1 - x ≤ 1 by linarith [hx.1])
            linarith
          have hneg_log : -x * Real.log x ≤ (1 / 1048576 : ℝ) * (20 * L) := by
            have hm : MonotoneOn (fun t => -t * Real.log t) (Set.Ioc (0 : ℝ) (1 / 4)) := by
              apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 (1 / 4))
              · intro t ht
                have ht0 : 0 < t := ht.1
                have hfun : (fun s => -s * Real.log s) = fun s => -(s * Real.log s) := by ext s; ring
                rw [hfun]
                exact ((hasDerivAt_id' t).fun_mul (Real.hasDerivAt_log (ne_of_gt ht0))).neg.continuousAt.continuousWithinAt
              · intro t ht; rw [interior_Ioc] at ht
                have hfun : (fun s => -s * Real.log s) = fun s => -(s * Real.log s) := by ext s; ring
                rw [hfun]
                exact ((hasDerivAt_id' t).fun_mul (Real.hasDerivAt_log (ne_of_gt ht.1))).neg.differentiableAt.differentiableWithinAt
              · intro t ht; rw [interior_Ioc] at ht
                have hd : HasDerivAt (fun s => -s * Real.log s) (-Real.log t - 1) t := by
                  have hfun : (fun s => -s * Real.log s) = fun s => -(s * Real.log s) := by ext s; ring
                  rw [hfun]
                  refine ((hasDerivAt_id' t).fun_mul (Real.hasDerivAt_log (ne_of_gt ht.1))).neg.congr_deriv ?_
                  field_simp [ne_of_gt ht.1]; ring
                rw [hd.deriv]
                have h4 : Real.log t ≤ Real.log (1 / 4) := Real.log_le_log ht.1 (le_of_lt ht.2)
                have hl4 : Real.log (1 / 4 : ℝ) = -(2 * L) := by
                  unfold L; have : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℤ) := by norm_num
                  rw [this, Real.log_zpow]; push_cast; ring
                linarith [L_gt_693]
            have hstep := hm ⟨hx.1, by linarith⟩ ⟨by norm_num, by norm_num⟩ hx20
            dsimp only at hstep
            have hl20 : Real.log (1 / 1048576 : ℝ) = -(20 * L) := by
              unfold L; have : (1 / 1048576 : ℝ) = (2 : ℝ) ^ (-20 : ℤ) := by norm_num
              rw [this, Real.log_zpow]; push_cast; ring
            rw [hl20] at hstep; linarith
          have h1 : 2 * x * (1 - x) * hp x ≤ 2 * (1 - x) * (-x * Real.log x) := by nlinarith [hx.1, hx.2]
          have h2 : 2 * (1 - x) * (-x * Real.log x) ≤ 2 * ((1 / 1048576 : ℝ) * (20 * L)) := by
            have hnn : 0 ≤ -x * Real.log x := by
              have := Real.log_nonpos (le_of_lt hx.1) (le_of_lt hx.2); nlinarith [hx.1]
            nlinarith [hx.1]
          linarith [L_lt_694, hx.1]
        · push Not at hlo
          have hhi : x ≤ (cLowHi : ℝ) / SCALE := by
            have : (cLowHi : ℝ) / SCALE = 1 / 2 := by unfold cLowHi SCALE; norm_num
            linarith
          have hpos := check1D_sound (P := fun u => 0 < (39 / 100 - 1 / 12 : ℝ) - (2 * (u * (1 - u)) * hp u - u))
            (fun X hok u hu => by
              unfold okCovLow at hok
              simp only [ivCBV_eq, fsub_eq, fmul_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
              have hu0 := pos_of_lo_pos hu hok.1.1.1
              have hu1 := pos_of_lo_pos (mem_sub mem_ONE hu) hok.1.2
              have hres := mem_sub (mem_sub mem_kapIv mem_r1_12Iv)
                (mem_sub (mem_mul (mem_mul (mem_ofInt 2) (mem_mul hu (mem_sub mem_ONE hu)))
                  (mem_fastHp hu hok.1.1.1 hok.1.2)) hu)
              have hgt := pos_of_lo_pos hres hok.2
              push_cast at hgt; linarith) chk_CovLow ⟨le_of_lt hlo, hhi⟩
          linarith
      · push Not at hhalf
        have hhp : hp x ≤ 0 := by
          unfold hp
          exact Real.log_nonpos (div_nonneg (by linarith [hx.2]) (le_of_lt hx.1))
            ((div_le_one hx.1).mpr (by linarith))
        nlinarith [hx.1, hx.2]
    have heq : 2 * hp x + (x + 39 / 100 - a) * hpp x
        = (2 * x * (1 - x) * hp x - x - (39 / 100 - a)) / (x * (1 - x)) := by
      unfold hpp; field_simp [ne_of_gt hx1m, ne_of_gt hx.1, show 1 - x ≠ 0 by linarith [hx.2]]; ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hx1m)

/-! ### Regime 2: Interior Mean `a ∈ [1/12, 2/3]` (`Fa_fun a x ≥ 0`) -/

private lemma mem_FaIv {A X : Interval} (hg : fGuardCovInt A X = true)
    {a x : ℝ} (ha : mem A a) (hx : mem X x) : mem (FaIv A X) (Fa_fun a x) := by
  unfold fGuardCovInt at hg
  simp only [ivCBV_eq, fsub_eq, fsq_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨ha0, _⟩, ha1⟩, _⟩, hgX⟩ := hg
  have ha_pos := pos_of_lo_pos ha ha0
  have ha_lt := pos_of_lo_pos (mem_sub mem_ONE ha) ha1
  have ⟨hx0, hx1⟩ := fGuardD1_bounds hgX hx
  have hres := mem_add
    (mem_sub
      (mem_add (mem_mul mem_kapIv (mem_mul hx (mem_divPos (mem_fastH ha (le_of_lt ha_pos) (by linarith : a ≤ 1)) ha ha0)))
               (mem_mul mem_deltaIv (mem_sub ha hx)))
      (mem_mul (mem_sub (mem_add hx mem_kapIv) ha) (mem_fastH hx (le_of_lt hx0) (le_of_lt hx1))))
    (mem_mul mem_CcovIv (mem_fastR validConstIv qL_lo_pos hx (le_of_lt hx0) (le_of_lt hx1)))
  have heq : (39 / 100 : ℝ) * (x * (h a / a)) + 7 / 10000 * (a - x)
      - (x + 39 / 100 - a) * h x + 13 / 25 * R_fun x = Fa_fun a x := by unfold Fa_fun; ring
  unfold FaIv; simp only [ivCBV_eq, fadd_eq, fsub_eq, fmul_eq, fdivPos_eq]
  rwa [heq] at hres

private lemma mem_FaDaIv {A X : Interval} (hg : fGuardCovInt A X = true)
    {a x : ℝ} (ha : mem A a) (hx : mem X x) : mem (FaDaIv A X) (Fa_da a x) := by
  unfold fGuardCovInt at hg
  simp only [ivCBV_eq, fsub_eq, fsq_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨_, _⟩, ha1⟩, ha2⟩, hgX⟩ := hg
  have ⟨hx0, hx1⟩ := fGuardD1_bounds hgX hx
  have hres := mem_add (mem_add (mem_mul mem_kapIv (mem_mul hx
      (mem_divPos (mem_fastLog (mem_sub mem_ONE ha) ha1) (mem_sq ha) ha2))) mem_deltaIv)
    (mem_fastH hx (le_of_lt hx0) (le_of_lt hx1))
  have heq : (39 / 100 : ℝ) * (x * (Real.log (1 - a) / a ^ 2)) + 7 / 10000 + h x = Fa_da a x := by
    unfold Fa_da; ring
  unfold FaDaIv; simp only [ivCBV_eq, fadd_eq, fmul_eq, fdivPos_eq, fsub_eq, fsq_eq]
  rwa [heq] at hres

private lemma mem_FaDxIv {A X : Interval} (hg : fGuardCovInt A X = true)
    {a x : ℝ} (ha : mem A a) (hx : mem X x) : mem (FaDxIv A X) (Fa_dx a x) := by
  unfold fGuardCovInt at hg
  simp only [ivCBV_eq, fsub_eq, fsq_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨ha0, _⟩, ha1⟩, _⟩, hgX⟩ := hg
  have ha_pos := pos_of_lo_pos ha ha0
  have ha_lt := pos_of_lo_pos (mem_sub mem_ONE ha) ha1
  have ⟨hx0, hx1⟩ := fGuardD1_bounds hgX hx
  have hgX' := hgX; unfold fGuardD1 at hgX'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgX'
  have hres := mem_add
    (mem_sub (mem_sub (mem_mul mem_kapIv (mem_divPos (mem_fastH ha (le_of_lt ha_pos) (by linarith : a ≤ 1)) ha ha0)) mem_deltaIv)
      (mem_add (mem_fastH hx (le_of_lt hx0) (le_of_lt hx1))
        (mem_mul (mem_sub (mem_add hx mem_kapIv) ha) (mem_fastHp hx hgX'.1.1.1.1.1.1.1 hgX'.1.1.1.1.1.2))))
    (mem_mul mem_CcovIv (mem_fastRP_of_guard hgX hx))
  have heq : (39 / 100 : ℝ) * (h a / a) - 7 / 10000 - (h x + (x + 39 / 100 - a) * hp x)
      + 13 / 25 * RP x = Fa_dx a x := by unfold Fa_dx; ring
  unfold FaDxIv; simp only [ivCBV_eq, fadd_eq, fsub_eq, fmul_eq, fdivPos_eq]
  rwa [heq] at hres

private lemma hasDerivAt_Fa_a {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun t => Fa_fun t x) (Fa_da a x) a := by
  have h1 := (hasDerivAt_h_div_id ha0 ha1).const_mul ((39 / 100 : ℝ) * x)
  have h2 := ((hasDerivAt_id' a).sub_const x).const_mul (7 / 10000 : ℝ)
  have h3 := (((hasDerivAt_const a (x + 39 / 100 : ℝ)).fun_sub (hasDerivAt_id' a)).mul_const (h x))
  have h4 := hasDerivAt_const a ((13 / 25 : ℝ) * R_fun x)
  have hfun : (fun t => Fa_fun t x) = fun t => ((39 / 100 : ℝ) * x) * (h t / t) + (7 / 10000 : ℝ) * (t - x)
      - (x + 39 / 100 - t) * h x + (13 / 25 : ℝ) * R_fun x := by ext t; unfold Fa_fun; ring
  rw [hfun]
  exact (((h1.fun_add h2).fun_sub h3).fun_add h4).congr_deriv (by unfold Fa_da; ring)

private lemma hasDerivAt_Fa_x {a x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun t => Fa_fun a t) (Fa_dx a x) x := by
  have h1 := (hasDerivAt_id' x).const_mul ((39 / 100 : ℝ) * (h a / a))
  have h2 := ((hasDerivAt_const x a).fun_sub (hasDerivAt_id' x)).const_mul (7 / 10000 : ℝ)
  have h3 := (((hasDerivAt_id' x).add_const (39 / 100 - a : ℝ)).fun_mul (hasDerivAt_h hx0 hx1))
  have h4 := (hasDerivAt_R hx0 hx1).const_mul (13 / 25 : ℝ)
  have hfun : (fun t => Fa_fun a t) = fun t => ((39 / 100 : ℝ) * (h a / a)) * t + (7 / 10000 : ℝ) * (a - t)
      - (t + (39 / 100 - a)) * h t + (13 / 25 : ℝ) * R_fun t := by ext t; unfold Fa_fun; ring
  rw [hfun]
  exact (((h1.fun_add h2).fun_sub h3).fun_add h4).congr_deriv (by unfold Fa_dx; ring)

private lemma cov_int_Fa_nonneg (hR_nn : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ R_fun x)
    {a x : ℝ} (ha1 : 1 / 12 ≤ a) (ha2 : a ≤ 2 / 3) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Fa_fun a x := by
  have hR := hR_nn x hx0 hx1
  have ha0 : 0 < a := by linarith
  have ha_lt : a < 1 := by linarith
  have h_ha_div : h (2 / 3 : ℝ) / (2 / 3 : ℝ) ≤ h a / a :=
    h_div_id_antitone ⟨ha0, le_of_lt ha_lt⟩ ⟨by norm_num, by norm_num⟩ ha2
  by_cases hL : x ≤ 1 / 65536
  · -- Analytic left tail x ∈ [0, 2^{-16}]
    have hh_le : h x ≤ h (1 / 65536 : ℝ) := h_mono_left ⟨hx0, by linarith⟩ ⟨by norm_num, by norm_num⟩ hL
    have hh_nn : 0 ≤ h x := h_nonneg hx0 hx1
    have h1 : 0 ≤ (39 / 100 : ℝ) * x * (h a / a) :=
      mul_nonneg (mul_nonneg (by norm_num) hx0) (div_nonneg (h_nonneg (le_of_lt ha0) (le_of_lt ha_lt)) (le_of_lt ha0))
    have hcoeff : x + 39 / 100 - a ≤ 1 / 65536 + 39 / 100 - 1 / 12 := by linarith
    have hprod : (x + 39 / 100 - a) * h x ≤ (1 / 65536 + 39 / 100 - 1 / 12 : ℝ) * (185 / 1000000) := by
      have h1' : (x + 39 / 100 - a) * h x ≤ (1 / 65536 + 39 / 100 - 1 / 12 : ℝ) * h x :=
        mul_le_mul_of_nonneg_right hcoeff hh_nn
      have h2' : (1 / 65536 + 39 / 100 - 1 / 12 : ℝ) * h x ≤ (1 / 65536 + 39 / 100 - 1 / 12 : ℝ) * (185 / 1000000) :=
        mul_le_mul_of_nonneg_left (le_of_lt (lt_of_le_of_lt hh_le h_inv65536_lt)) (by norm_num)
      linarith
    unfold Fa_fun; linarith
  · push Not at hL
    by_cases hRstrip : 255 / 256 ≤ x
    · -- Analytic right tail x ∈ [1 - 2^{-8}, 1]
      have hh_le : h x ≤ h (255 / 256 : ℝ) := h_anti_right ⟨by norm_num, by norm_num⟩ ⟨by linarith, hx1⟩ hRstrip
      have hh_nn : 0 ≤ h x := h_nonneg hx0 hx1
      have hha_lb : (954 / 1000 : ℝ) ≤ h a / a := by linarith [h_two_thirds_gt]
      have h1 : (39 / 100 : ℝ) * (255 / 256) * (954 / 1000) ≤ (39 / 100 : ℝ) * x * (h a / a) := by nlinarith
      have hprod : (x + 39 / 100 - a) * h x ≤ (1 + 39 / 100 - 1 / 12 : ℝ) * (26 / 1000) := by
        have h1' : (x + 39 / 100 - a) * h x ≤ (1 + 39 / 100 - 1 / 12 : ℝ) * h x :=
          mul_le_mul_of_nonneg_right (by linarith) hh_nn
        have h2' : (1 + 39 / 100 - 1 / 12 : ℝ) * h x ≤ (1 + 39 / 100 - 1 / 12 : ℝ) * (26 / 1000) :=
          mul_le_mul_of_nonneg_left (le_of_lt (lt_of_le_of_lt hh_le h_255_256_lt)) (by norm_num)
        linarith
      unfold Fa_fun; linarith
    · -- Certified 2D tree on [1/12, 2/3] × [2^{-16}, 1 - 2^{-8}]
      push Not at hRstrip
      have hS := SCALE_pos
      have ha_mem : mem ⟨ca1, ca2⟩ a := by
        constructor
        · have : (ca1 : ℝ) / SCALE ≤ 1 / 12 := by unfold ca1 SCALE; norm_num
          linarith
        · have : (2 / 3 : ℝ) ≤ (ca2 : ℝ) / SCALE := by unfold ca2 SCALE; norm_num
          linarith
      have hx_mem : mem ⟨cx1, cx2⟩ x := by
        constructor
        · have : (cx1 : ℝ) / SCALE = 1 / 65536 := by unfold cx1 SCALE; norm_num
          linarith
        · have : (cx2 : ℝ) / SCALE = 255 / 256 := by unfold cx2 SCALE; norm_num
          linarith
      exact le_of_lt (check2DW_sound (P := fun u v => 0 < Fa_fun u v) (fun w A X hok u v hu hv => by
        unfold okCovInt at hok; simp only [Bool.and_eq_true] at hok
        have hg := hok.1
        have hg' := hg; unfold fGuardCovInt at hg'
        simp only [ivCBV_eq, fsub_eq, fsq_eq, Bool.and_eq_true, decide_eq_true_eq] at hg'
        have hgX := hg'.2
        have hgX' := hgX; unfold fGuardD1 at hgX'
        simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgX'
        have hAle : A.lo ≤ A.hi := hg'.1.1.1.2
        have hXle : X.lo ≤ X.hi := hgX'.1.1.1.1.1.1.2
        have hA01 : ∀ t, mem A t → 0 < t ∧ t < 1 := fun t ht =>
          ⟨pos_of_lo_pos ht hg'.1.1.1.1, by linarith [pos_of_lo_pos (mem_sub mem_ONE ht) hg'.1.1.2]⟩
        exact centered2DWPos_sound hAle hXle
          (fun I J hIlo hIhi hJlo hJhi s t hs ht => by
            have hsA : mem A s := ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hIlo) (le_of_lt hS)) hs.1,
              le_trans hs.2 (div_le_div_of_nonneg_right (by exact_mod_cast hIhi) (le_of_lt hS))⟩
            have htX : mem X t := ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hJlo) (le_of_lt hS)) ht.1,
              le_trans ht.2 (div_le_div_of_nonneg_right (by exact_mod_cast hJhi) (le_of_lt hS))⟩
            have hI0 : 0 < I.lo := lt_of_lt_of_le hg'.1.1.1.1 hIlo
            have hI1 : 0 < (sub ONE I).lo := by
              have hA1 := hg'.1.1.2; unfold sub ONE at hA1 ⊢; dsimp only at hA1 ⊢; omega
            have hIA : mem I s := hs; have hJX : mem J t := ht
            have hst_a := hA01 s hsA
            have hst_x := fGuardD1_bounds hgX htX
            have hres := mem_add
              (mem_sub
                (mem_add (mem_mul mem_kapIv (mem_mul ht (mem_divPos (mem_fastH hs (le_of_lt hst_a.1) (le_of_lt hst_a.2)) hs hI0)))
                         (mem_mul mem_deltaIv (mem_sub hs ht)))
                (mem_mul (mem_sub (mem_add ht mem_kapIv) hs) (mem_fastH ht (le_of_lt hst_x.1) (le_of_lt hst_x.2))))
              (mem_mul mem_CcovIv (mem_fastR validConstIv qL_lo_pos ht (le_of_lt hst_x.1) (le_of_lt hst_x.2)))
            have heq : (39 / 100 : ℝ) * (t * (h s / s)) + 7 / 10000 * (s - t)
                - (t + 39 / 100 - s) * h t + 13 / 25 * R_fun t = Fa_fun s t := by unfold Fa_fun; ring
            unfold FaIv; simp only [ivCBV_eq, fadd_eq, fsub_eq, fmul_eq, fdivPos_eq]
            rwa [heq] at hres)
          (fun s t hs ht => mem_FaDaIv hg hs ht)
          (fun t ht => by
            set ma := (A.lo + A.hi) / 2
            have hma_lo : A.lo ≤ ma := by omega
            have hma_hi : ma ≤ A.hi := by omega
            have hmaA : mem A ((ma : ℝ) / SCALE) :=
              ⟨div_le_div_of_nonneg_right (by exact_mod_cast hma_lo) (le_of_lt hS),
               div_le_div_of_nonneg_right (by exact_mod_cast hma_hi) (le_of_lt hS)⟩
            have hma0 : 0 < (pt ma).lo := by unfold pt; dsimp only; omega
            have hma1 : 0 < (sub ONE (pt ma)).lo := by
              have hA1 := hg'.1.1.2; unfold sub ONE at hA1 ⊢; unfold pt; dsimp only at hA1 ⊢; omega
            have hmas : 0 < (Iv.sq (pt ma)).lo := by
              have hAsq := hg'.1.2
              have hle : A.lo * A.lo ≤ ma * ma := by nlinarith [hg'.1.1.1.1]
              unfold Iv.sq at hAsq ⊢
              simp only [le_of_lt hg'.1.1.1.1, ↓reduceIte] at hAsq
              simp only [show 0 ≤ (pt ma).lo by unfold pt; dsimp only; omega, ↓reduceIte]
              unfold pt; dsimp only; unfold fdiv at hAsq ⊢
              exact lt_of_lt_of_le hAsq (Int.ediv_le_ediv (by decide : (0 : ℤ) < SCALE) hle)
            have hgm : fGuardCovInt (pt ma) X = true := by
              unfold fGuardCovInt; simp only [ivCBV_eq, fsub_eq, fsq_eq, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨⟨⟨⟨hma0, le_rfl⟩, hma1⟩, hmas⟩, hgX⟩
            exact mem_FaDxIv hgm (mem_pt ma) ht)
          (fun t _ s hs => (hasDerivAt_Fa_a (hA01 s hs).1 (hA01 s hs).2).continuousAt.continuousWithinAt)
          (fun t _ s hs => hasDerivAt_Fa_a (hA01 s (Set.Ioo_subset_Icc_self hs)).1 (hA01 s (Set.Ioo_subset_Icc_self hs)).2)
          (fun t ht => (hasDerivAt_Fa_x (fGuardD1_bounds hgX ht).1 (fGuardD1_bounds hgX ht).2).continuousAt.continuousWithinAt)
          (fun t ht => hasDerivAt_Fa_x (fGuardD1_bounds hgX (Set.Ioo_subset_Icc_self ht)).1 (fGuardD1_bounds hgX (Set.Ioo_subset_Icc_self ht)).2)
          hok.2 hu hv) chk_CovInt ha_mem hx_mem)

/-! ### Regime 3: High Mean `a ∈ (2/3, 1)` (`Ghi_fun a x ≥ 0`) -/

private lemma hasDerivAt_Ghi_a {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun t => Ghi_fun t x) (Ghi_da a x) a := by
  have h1 : HasDerivAt (fun t => KL_fun x t) ((a - x) / (a * (1 - a))) a := by
    have hl1 := (Real.hasDerivAt_log (ne_of_gt ha0)).const_mul x
    have hl2 : HasDerivAt (fun t => (1 - x) * Real.log (1 - t)) ((1 - x) * (-1 / (1 - a))) a := by
      have hsub : HasDerivAt (fun t => 1 - t) (-1) a := by simpa using (hasDerivAt_const a (1 : ℝ)).fun_sub (hasDerivAt_id' a)
      exact (HasDerivAt.comp (h := fun t => 1 - t) a (Real.hasDerivAt_log (by linarith)) hsub).const_mul (1 - x) |>.congr_deriv (by ring)
    have hfun : (fun t => KL_fun x t) = fun t => -h x - x * Real.log t - (1 - x) * Real.log (1 - t) := rfl
    rw [hfun]
    exact (((hasDerivAt_const a (-h x)).fun_sub hl1).fun_sub hl2).congr_deriv (by
      field_simp [ne_of_gt ha0, show 1 - a ≠ 0 by linarith]; ring)
  have h2 : HasDerivAt (fun t => (t - x) * (h t - h x)) ((h a - h x) + (a - x) * hp a) a := by
    have hd1 : HasDerivAt (fun t => t - x) 1 a := by simpa using (hasDerivAt_id' a).sub_const x
    have hd2 : HasDerivAt (fun t => h t - h x) (hp a) a := (hasDerivAt_h ha0 ha1).sub_const (h x)
    exact (hd1.fun_mul hd2).congr_deriv (by ring)
  exact ((h1.const_mul (39 / 100 : ℝ)).fun_sub h2).congr_deriv (by unfold Ghi_da; ring)

private lemma hasDerivAt_Ghi_x {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun t => Ghi_fun a t) (Ghi_dx a x) x := by
  have h1 : HasDerivAt (fun t => KL_fun t a) (hp a - hp x) x := by
    have hfun : (fun t => KL_fun t a) = fun t => h a + (t - a) * hp a - h t := by
      ext t; exact KL_eq_tangent ha0 ha1
    rw [hfun]
    have hd1 : HasDerivAt (fun t => h a + (t - a) * hp a) (hp a) x := by
      have := (((hasDerivAt_id' x).sub_const a).mul_const (hp a)).const_add (h a)
      exact this.congr_deriv (by ring)
    exact hd1.fun_sub (hasDerivAt_h hx0 hx1)
  have h2 : HasDerivAt (fun t => (a - t) * (h a - h t)) (-(h a - h x) - (a - x) * hp x) x := by
    have hd1 : HasDerivAt (fun t => a - t) (-1) x := by simpa using (hasDerivAt_const x a).fun_sub (hasDerivAt_id' x)
    have hd2 : HasDerivAt (fun t => h a - h t) (-hp x) x := by
      simpa using (hasDerivAt_const x (h a)).fun_sub (hasDerivAt_h hx0 hx1)
    exact (hd1.fun_mul hd2).congr_deriv (by ring)
  exact ((h1.const_mul (39 / 100 : ℝ)).fun_sub h2).congr_deriv (by unfold Ghi_dx; ring)

private lemma cov_hi_Ghi_nonneg {a x : ℝ} (ha1 : 2 / 3 < a) (ha2 : a < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ Ghi_fun a x := by
  have ha0 : 0 < a := by linarith
  by_cases hge : 1 - a ≤ x
  · -- x ≥ 1 - a: (a - x)(h a - h x) ≤ 0, so Ghi_fun a x ≥ (39/100) * KL ≥ 0!
    have hkl := KL_nonneg hx0 hx1 ha0 ha2
    have hprod : (a - x) * (h a - h x) ≤ 0 := by
      rcases le_total x a with hxa | hax
      · -- 1 - a ≤ x ≤ a: h x ≥ h a
        have hhx : h a ≤ h x := by
          rcases le_total x (1 / 2) with hx5 | hx5
          · rw [← h_symm a]; exact h_mono_left ⟨by linarith, by linarith⟩ ⟨hx0, hx5⟩ hge
          · exact h_anti_right ⟨hx5, hx1⟩ ⟨by linarith, le_of_lt ha2⟩ hxa
        nlinarith
      · -- a ≤ x: h x ≤ h a
        have hhx : h x ≤ h a := h_anti_right ⟨by linarith, le_of_lt ha2⟩ ⟨by linarith, hx1⟩ hax
        nlinarith
    unfold Ghi_fun; linarith
  · push Not at hge
    -- Now x < 1 - a < 1/3
    by_cases ha15 : 15 / 16 ≤ a
    · -- Analytic high-a tail: a ∈ [15/16, 1), x < 1 - a ≤ 1/16
      have hx16 : x ≤ 1 / 16 := by linarith
      have hha : h a ≤ h (1 / 16 : ℝ) := by
        rw [← h_symm a]; exact h_mono_left ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ (by linarith)
      have hhx : h x ≤ h (1 / 16 : ℝ) := h_mono_left ⟨hx0, by linarith⟩ ⟨by norm_num, by norm_num⟩ hx16
      have hlog_a : Real.log a ≤ 0 := Real.log_nonpos (le_of_lt ha0) (le_of_lt ha2)
      have hlog_1ma : Real.log (1 - a) ≤ -(4 * L) := by
        have h1 : Real.log (1 - a) ≤ Real.log (1 / 16) := Real.log_le_log (by linarith) (by linarith)
        have h2 : Real.log (1 / 16 : ℝ) = -(4 * L) := by
          unfold L; have : (1 / 16 : ℝ) = (2 : ℝ) ^ (-4 : ℤ) := by norm_num
          rw [this, Real.log_zpow]; push_cast; ring
        linarith
      have hkl_lb : (15 / 16 : ℝ) * (4 * L) - h (1 / 16 : ℝ) ≤ KL_fun x a := by
        unfold KL_fun
        have h1 : 0 ≤ -x * Real.log a := by nlinarith
        have h2 : (15 / 16 : ℝ) * (4 * L) ≤ -(1 - x) * Real.log (1 - a) := by
          have : 4 * L ≤ -Real.log (1 - a) := by linarith
          nlinarith [L_pos]
        linarith
      have hprod_ub : (a - x) * (h a - h x) ≤ h (1 / 16 : ℝ) := by
        have h1 : h a - h x ≤ h (1 / 16 : ℝ) := by linarith [h_nonneg hx0 hx1]
        have h2 : 0 ≤ a - x := by linarith
        have h3 : a - x ≤ 1 := by linarith
        nlinarith [h_nonneg (show (0 : ℝ) ≤ 1 / 16 by norm_num) (by norm_num)]
      unfold Ghi_fun
      linarith [h_1_16_lt, L_gt_693]
    · push Not at ha15
      -- Now a ∈ (2/3, 15/16) and x < 1 - a < 1/3
      by_cases hx12 : x ≤ 1 / 4096
      · -- Analytic small-x tail: P(a, x) = P(a, 0) + (a - κ - x) h(x) + x (h(a) + κ log((1-a)/a))
        have hdecomp : Ghi_fun a x = ((39 / 100 : ℝ) * (-Real.log (1 - a)) - a * h a)
            + (a - 39 / 100 - x) * h x
            + x * (h a + (39 / 100 : ℝ) * (Real.log (1 - a) - Real.log a)) := by
          unfold Ghi_fun KL_fun; ring
        -- f(a) = (39/100)*(-log(1-a)) - a*h(a) is monotone increasing on [2/3, 15/16]
        have hf_mono : MonotoneOn (fun t => (39 / 100 : ℝ) * (-Real.log (1 - t)) - t * h t) (Set.Icc (2 / 3 : ℝ) (15 / 16)) := by
          apply monotoneOn_of_deriv_nonneg (convex_Icc (2 / 3) (15 / 16))
          · intro t ht
            have ht0 : 0 < t := by linarith [ht.1]
            have ht1 : t < 1 := by linarith [ht.2]
            have hd1 : HasDerivAt (fun s => (39 / 100 : ℝ) * (-Real.log (1 - s))) ((39 / 100) / (1 - t)) t := by
              have hsub : HasDerivAt (fun s => 1 - s) (-1) t := by simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)
              have hl := (HasDerivAt.comp (h := fun s => 1 - s) t (Real.hasDerivAt_log (by linarith)) hsub).neg.const_mul (39 / 100 : ℝ)
              exact hl.congr_deriv (by ring)
            have hd2 : HasDerivAt (fun s => s * h s) (h t + t * hp t) t := by
              exact ((hasDerivAt_id' t).fun_mul (hasDerivAt_h ht0 ht1)).congr_deriv (by ring)
            exact (hd1.fun_sub hd2).continuousAt.continuousWithinAt
          · intro t ht; rw [interior_Icc] at ht
            have ht0 : 0 < t := by linarith [ht.1]
            have ht1 : t < 1 := by linarith [ht.2]
            have hd1 : HasDerivAt (fun s => (39 / 100 : ℝ) * (-Real.log (1 - s))) ((39 / 100) / (1 - t)) t := by
              have hsub : HasDerivAt (fun s => 1 - s) (-1) t := by simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)
              have hl := (HasDerivAt.comp (h := fun s => 1 - s) t (Real.hasDerivAt_log (by linarith)) hsub).neg.const_mul (39 / 100 : ℝ)
              exact hl.congr_deriv (by ring)
            have hd2 : HasDerivAt (fun s => s * h s) (h t + t * hp t) t := by
              exact ((hasDerivAt_id' t).fun_mul (hasDerivAt_h ht0 ht1)).congr_deriv (by ring)
            exact (hd1.fun_sub hd2).differentiableAt.differentiableWithinAt
          · intro t ht; rw [interior_Icc] at ht
            have ht0 : 0 < t := by linarith [ht.1]
            have ht1 : t < 1 := by linarith [ht.2]
            have hd : HasDerivAt (fun s => (39 / 100 : ℝ) * (-Real.log (1 - s)) - s * h s)
                ((39 / 100) / (1 - t) - (h t + t * hp t)) t := by
              have hsub : HasDerivAt (fun s => 1 - s) (-1) t := by simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id' t)
              have hl := (HasDerivAt.comp (h := fun s => 1 - s) t (Real.hasDerivAt_log (by linarith)) hsub).neg.const_mul (39 / 100 : ℝ)
              have hd2 := ((hasDerivAt_id' t).fun_mul (hasDerivAt_h ht0 ht1))
              exact (hl.fun_sub hd2).congr_deriv (by ring)
            rw [hd.deriv]
            have h1 : (39 / 100 : ℝ) * 3 ≤ (39 / 100) / (1 - t) := by
              rw [le_div_iff₀ (by linarith)]; nlinarith [ht.1]
            have hhp : hp t ≤ 0 := by
              unfold hp
              exact Real.log_nonpos (div_nonneg (by linarith) (le_of_lt ht0)) ((div_le_one ht0).mpr (by linarith [ht.1]))
            have hh : h t ≤ L := h_le_L (le_of_lt ht0) (le_of_lt ht1)
            nlinarith [L_lt_694]
        have hf_lb : (39 / 100 : ℝ) * Real.log 3 - (2 / 3) * h (2 / 3)
            ≤ (39 / 100 : ℝ) * (-Real.log (1 - a)) - a * h a := by
          have hstep := hf_mono ⟨le_rfl, by norm_num⟩ ⟨le_of_lt ha1, le_of_lt ha15⟩ (le_of_lt ha1)
          dsimp only at hstep
          have h3 : -Real.log (1 - (2 / 3 : ℝ)) = Real.log 3 := by
            have : (1 - (2 / 3 : ℝ)) = (3 : ℝ)⁻¹ := by norm_num
            rw [this, Real.log_inv]; ring
          rwa [h3] at hstep
        have hterm2 : 0 ≤ (a - 39 / 100 - x) * h x :=
          mul_nonneg (by linarith) (h_nonneg hx0 hx1)
        have hlog_ratio : -Real.log 15 ≤ Real.log (1 - a) - Real.log a := by
          rw [← Real.log_div (by linarith) (ne_of_gt ha0), ← Real.log_inv]
          exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ ha0]; linarith)
        have hterm3 : -(1 / 4096 : ℝ) * ((39 / 100) * (271 / 100))
            ≤ x * (h a + (39 / 100 : ℝ) * (Real.log (1 - a) - Real.log a)) := by
          have h1 : -((39 / 100 : ℝ) * (271 / 100)) ≤ h a + (39 / 100 : ℝ) * (Real.log (1 - a) - Real.log a) := by
            linarith [h_nonneg (le_of_lt ha0) (le_of_lt ha2), log_15_lt]
          nlinarith
        rw [hdecomp]
        linarith [log_3_gt, h_two_thirds_lt]
      · -- Certified 2D tree on [2/3, 15/16] × [2^{-12}, 1/3] with x < 1 - a
        push Not at hx12
        have hS := SCALE_pos
        have ha_mem : mem ⟨ca3, ca4⟩ a := by
          constructor
          · have : (ca3 : ℝ) / SCALE ≤ 2 / 3 := by unfold ca3 SCALE; norm_num
            linarith
          · have : (15 / 16 : ℝ) ≤ (ca4 : ℝ) / SCALE := by unfold ca4 SCALE; norm_num
            linarith
        have hx_mem : mem ⟨cxh1, cxh2⟩ x := by
          constructor
          · have : (cxh1 : ℝ) / SCALE = 1 / 4096 := by unfold cxh1 SCALE; norm_num
            linarith
          · have : (1 / 3 : ℝ) ≤ (cxh2 : ℝ) / SCALE := by unfold cxh2 SCALE; norm_num
            linarith
        exact le_of_lt (check2DW_sound (P := fun u v => v < 1 - u → 0 < Ghi_fun u v)
          (fun w A X hok u v hu hv huv => by
            cases w with
            | skip =>
              unfold okCovHi at hok; simp only [decide_eq_true_eq] at hok
              have h1 : ((SCALE - A.lo : ℤ) : ℝ) / SCALE ≤ (X.lo : ℝ) / SCALE :=
                div_le_div_of_nonneg_right (by exact_mod_cast hok) (le_of_lt hS)
              have h2 : ((SCALE - A.lo : ℤ) : ℝ) / SCALE = 1 - (A.lo : ℝ) / SCALE := by
                push_cast; rw [sub_div, div_self (ne_of_gt hS)]
              linarith [hu.1, hv.1]
            | _ =>
              unfold okCovHi at hok; simp only [Bool.and_eq_true] at hok
              have hg := hok.1
              have hg' := hg; unfold fGuardCovHi at hg'
              simp only [ivCBV_eq, fsub_eq, fmul_eq, Bool.and_eq_true, decide_eq_true_eq] at hg'
              have hAle : A.lo ≤ A.hi := hg'.1.1.1.1.1.2
              have hXle : X.lo ≤ X.hi := hg'.1.2
              have hA01 : ∀ t, mem A t → 0 < t ∧ t < 1 := fun t ht =>
                ⟨pos_of_lo_pos ht hg'.1.1.1.1.1.1, by linarith [pos_of_lo_pos (mem_sub mem_ONE ht) hg'.1.1.1.1.2]⟩
              have hX01 : ∀ t, mem X t → 0 < t ∧ t < 1 := fun t ht =>
                ⟨pos_of_lo_pos ht hg'.1.1.2, by linarith [pos_of_lo_pos (mem_sub mem_ONE ht) hg'.2]⟩
              exact centered2DWPos_sound (G := Ghi_fun) (Gx := Ghi_da) (Gy := Ghi_dx) hAle hXle
                (fun I J hIlo hIhi hJlo hJhi s t hs ht => by
                  have hI0 : 0 < I.lo := lt_of_lt_of_le hg'.1.1.1.1.1.1 hIlo
                  have hI1 : 0 < (sub ONE I).lo := by
                    have hA1 := hg'.1.1.1.1.2; unfold sub ONE at hA1 ⊢; dsimp only at hA1 ⊢; omega
                  have hst_a : 0 < s ∧ s < 1 :=
                    ⟨pos_of_lo_pos hs hI0, by linarith [pos_of_lo_pos (mem_sub mem_ONE hs) hI1]⟩
                  have hJ0 : 0 < J.lo := lt_of_lt_of_le hg'.1.1.2 hJlo
                  have hJ1 : 0 < (sub ONE J).lo := by
                    have hX1 := hg'.2; unfold sub ONE at hX1 ⊢; dsimp only at hX1 ⊢; omega
                  have hst_x : 0 < t ∧ t < 1 :=
                    ⟨pos_of_lo_pos ht hJ0, by linarith [pos_of_lo_pos (mem_sub mem_ONE ht) hJ1]⟩
                  have hkl := mem_sub (mem_sub (mem_neg (mem_fastH ht (le_of_lt hst_x.1) (le_of_lt hst_x.2)))
                      (mem_mul ht (mem_fastLog hs hI0)))
                    (mem_mul (mem_sub mem_ONE ht) (mem_fastLog (mem_sub mem_ONE hs) hI1))
                  have hres := mem_sub (mem_mul mem_kapIv hkl)
                    (mem_mul (mem_sub hs ht) (mem_sub (mem_fastH hs (le_of_lt hst_a.1) (le_of_lt hst_a.2))
                      (mem_fastH ht (le_of_lt hst_x.1) (le_of_lt hst_x.2))))
                  have heq : (39 / 100 : ℝ) * (-h t - t * Real.log s - (1 - t) * Real.log (1 - s))
                      - (s - t) * (h s - h t) = Ghi_fun s t := rfl
                  unfold GhiIv KLIv; simp only [ivCBV_eq, fsub_eq, fmul_eq, fneg_eq]
                  rwa [heq] at hres)
                (fun s t hs ht => by
                  have ha' := hA01 s hs; have hx' := hX01 t ht
                  have hres := mem_sub
                    (mem_sub (mem_mul mem_kapIv (mem_divPos (mem_sub hs ht) (mem_mul hs (mem_sub mem_ONE hs)) hg'.1.1.1.2))
                      (mem_sub (mem_fastH hs (le_of_lt ha'.1) (le_of_lt ha'.2)) (mem_fastH ht (le_of_lt hx'.1) (le_of_lt hx'.2))))
                    (mem_mul (mem_sub hs ht) (mem_fastHp hs hg'.1.1.1.1.1.1 hg'.1.1.1.1.2))
                  have heq : (39 / 100 : ℝ) * ((s - t) / (s * (1 - s))) - (h s - h t) - (s - t) * hp s = Ghi_da s t := rfl
                  unfold GhiDaIv; simp only [ivCBV_eq, fsub_eq, fmul_eq, fdivPos_eq]
                  rwa [heq] at hres)
                (fun t ht => by
                  set ma := (A.lo + A.hi) / 2
                  have hma_lo : A.lo ≤ ma := by omega
                  have hma_hi : ma ≤ A.hi := by omega
                  have hma0 : 0 < (pt ma).lo := by unfold pt; dsimp only; omega
                  have hma1 : 0 < (sub ONE (pt ma)).lo := by
                    have hA1 := hg'.1.1.1.1.2; unfold sub ONE at hA1 ⊢; unfold pt; dsimp only at hA1 ⊢; omega
                  have hmaA : mem A ((ma : ℝ) / SCALE) :=
                    ⟨div_le_div_of_nonneg_right (by exact_mod_cast hma_lo) (le_of_lt hS),
                     div_le_div_of_nonneg_right (by exact_mod_cast hma_hi) (le_of_lt hS)⟩
                  have ha' := hA01 _ hmaA; have hx' := hX01 t ht
                  have hres := mem_add
                    (mem_add (mem_mul mem_kapIv (mem_sub (mem_fastHp (mem_pt ma) hma0 hma1) (mem_fastHp ht hg'.1.1.2 hg'.2)))
                      (mem_sub (mem_fastH (mem_pt ma) (le_of_lt ha'.1) (le_of_lt ha'.2)) (mem_fastH ht (le_of_lt hx'.1) (le_of_lt hx'.2))))
                    (mem_mul (mem_sub (mem_pt ma) ht) (mem_fastHp ht hg'.1.1.2 hg'.2))
                  have heq : (39 / 100 : ℝ) * (hp ((ma : ℝ) / SCALE) - hp t)
                      + (h ((ma : ℝ) / SCALE) - h t) + ((ma : ℝ) / SCALE - t) * hp t = Ghi_dx ((ma : ℝ) / SCALE) t := rfl
                  unfold GhiDxIv; simp only [ivCBV_eq, fadd_eq, fsub_eq, fmul_eq]
                  rwa [heq] at hres)
                (fun t _ s hs => (hasDerivAt_Ghi_a (hA01 s hs).1 (hA01 s hs).2).continuousAt.continuousWithinAt)
                (fun t _ s hs => hasDerivAt_Ghi_a (hA01 s (Set.Ioo_subset_Icc_self hs)).1 (hA01 s (Set.Ioo_subset_Icc_self hs)).2)
                (fun t ht => by
                  set ma := (A.lo + A.hi) / 2
                  have hmaA : mem A ((ma : ℝ) / SCALE) :=
                    ⟨div_le_div_of_nonneg_right (by exact_mod_cast (by omega : A.lo ≤ ma)) (le_of_lt hS),
                     div_le_div_of_nonneg_right (by exact_mod_cast (by omega : ma ≤ A.hi)) (le_of_lt hS)⟩
                  exact (hasDerivAt_Ghi_x (hA01 _ hmaA).1 (hA01 _ hmaA).2 (hX01 t ht).1 (hX01 t ht).2).continuousAt.continuousWithinAt)
                (fun t ht => by
                  set ma := (A.lo + A.hi) / 2
                  have hmaA : mem A ((ma : ℝ) / SCALE) :=
                    ⟨div_le_div_of_nonneg_right (by exact_mod_cast (by omega : A.lo ≤ ma)) (le_of_lt hS),
                     div_le_div_of_nonneg_right (by exact_mod_cast (by omega : ma ≤ A.hi)) (le_of_lt hS)⟩
                  exact hasDerivAt_Ghi_x (hA01 _ hmaA).1 (hA01 _ hmaA).2
                    (hX01 t (Set.Ioo_subset_Icc_self ht)).1 (hX01 t (Set.Ioo_subset_Icc_self ht)).2)
                hok.2 hu hv) chk_CovHi ha_mem hx_mem hge)

/-! ### Master Theorem: `cert_Cov` (`LocalInequalities.hCov`) -/

theorem cert_Cov (hR_nn : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ R_fun x) :
    ∀ {ι : Type} (s : Finset ι) (w Y : ι → ℝ),
      (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) → (∀ i ∈ s, 0 ≤ Y i ∧ Y i ≤ 1) →
      let a := ∑ i ∈ s, w i * Y i
      (∑ i ∈ s, w i * (Y i - a) * h (Y i))
        ≤ kappaParam * (h a - ∑ i ∈ s, w i * h (Y i)) + CcovParam * ∑ i ∈ s, w i * R_fun (Y i) := by
  intro ι s w Y hw hsum hY a
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hY i hi).1
  have ha1 : a ≤ 1 := by
    calc a = ∑ i ∈ s, w i * Y i := rfl
      _ ≤ ∑ i ∈ s, w i * 1 := Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hY i hi).2 (hw i hi)
      _ = 1 := by simp [hsum]
  have hR_sum : 0 ≤ ∑ i ∈ s, w i * R_fun (Y i) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hR_nn (Y i) (hY i hi).1 (hY i hi).2)
  rcases ha0.eq_or_lt with ha_eq0 | ha_pos
  · -- a = 0: every i with w i > 0 has Y i = 0, hence h(Y i) = 0
    have hzero : ∀ i ∈ s, w i * Y i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i hi => mul_nonneg (hw i hi) (hY i hi).1).mp ha_eq0.symm
    have hterm : ∀ i ∈ s, w i * h (Y i) = 0 := fun i hi => by
      rcases mul_eq_zero.mp (hzero i hi) with hwi | hYi
      · simp [hwi]
      · simp [hYi, h_zero]
    have hL0 : ∑ i ∈ s, w i * (Y i - a) * h (Y i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rcases mul_eq_zero.mp (hzero i hi) with hwi | hYi
        · simp [hwi]
        · simp [hYi, h_zero]
    have hE0 : ∑ i ∈ s, w i * h (Y i) = 0 := Finset.sum_eq_zero hterm
    rw [hL0, hE0, ← ha_eq0, h_zero]; unfold kappaParam CcovParam; linarith
  rcases ha1.eq_or_lt with ha_eq1 | ha_lt1
  · -- a = 1: every i with w i > 0 has Y i = 1, hence h(Y i) = 0
    have hsum1 : ∑ i ∈ s, w i * (1 - Y i) = 0 := by
      have : ∑ i ∈ s, w i * (1 - Y i) = (∑ i ∈ s, w i) - a := by
        simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]; rfl
      linarith
    have hzero : ∀ i ∈ s, w i * (1 - Y i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i hi => mul_nonneg (hw i hi) (by linarith [(hY i hi).2])).mp hsum1
    have hL0 : ∑ i ∈ s, w i * (Y i - a) * h (Y i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rcases mul_eq_zero.mp (hzero i hi) with hwi | hYi
        · simp [hwi]
        · have : Y i = 1 := by linarith
          simp [this, h_one]
    have hE0 : ∑ i ∈ s, w i * h (Y i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rcases mul_eq_zero.mp (hzero i hi) with hwi | hYi
        · simp [hwi]
        · have : Y i = 1 := by linarith
          simp [this, h_one]
    rw [hL0, hE0, ha_eq1, h_one]; unfold kappaParam CcovParam; linarith
  -- Now 0 < a < 1: split into three regimes!
  unfold kappaParam CcovParam
  by_cases h1 : a < 1 / 12
  · -- Regime 1: Low mean via concavity + Jensen
    have hconc := cov_low_mean ha_pos h1
    have hj := hconc.le_map_sum hw hsum (fun i hi => hY i hi)
    simp only [smul_eq_mul] at hj
    have ha_rew : ∑ i ∈ s, w i * Y i = a := rfl
    rw [ha_rew] at hj
    have hlhs : ∑ i ∈ s, w i * ((Y i + 39 / 100 - a) * h (Y i))
        = (∑ i ∈ s, w i * (Y i - a) * h (Y i)) + (39 / 100 : ℝ) * ∑ i ∈ s, w i * h (Y i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    have hrhs : (a + 39 / 100 - a) * h a = (39 / 100 : ℝ) * h a := by ring
    linarith
  · push Not at h1
    by_cases h2 : a ≤ 2 / 3
    · -- Regime 2: Interior mean via ∑ w_i Fa(a, Y_i) ≥ 0
      have hsum_nn : 0 ≤ ∑ i ∈ s, w i * Fa_fun a (Y i) :=
        Finset.sum_nonneg fun i hi =>
          mul_nonneg (hw i hi) (cov_int_Fa_nonneg hR_nn h1 h2 (hY i hi).1 (hY i hi).2)
      have hsum_eq : ∑ i ∈ s, w i * Fa_fun a (Y i)
          = (39 / 100 : ℝ) * (h a - ∑ i ∈ s, w i * h (Y i))
            + (13 / 25 : ℝ) * (∑ i ∈ s, w i * R_fun (Y i))
            - ∑ i ∈ s, w i * (Y i - a) * h (Y i) := by
        have hpart1 : ∑ i ∈ s, w i * ((39 / 100 : ℝ) * Y i * (h a / a)) = (39 / 100 : ℝ) * h a := by
          have : ∑ i ∈ s, w i * ((39 / 100 : ℝ) * Y i * (h a / a))
              = (39 / 100 : ℝ) * (h a / a) * (∑ i ∈ s, w i * Y i) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
          rw [this, show ∑ i ∈ s, w i * Y i = a from rfl]
          field_simp [ne_of_gt ha_pos]
        have hpart2 : ∑ i ∈ s, w i * ((7 / 10000 : ℝ) * (a - Y i)) = 0 := by
          have : ∑ i ∈ s, w i * ((7 / 10000 : ℝ) * (a - Y i))
              = (7 / 10000 : ℝ) * (a * (∑ i ∈ s, w i) - ∑ i ∈ s, w i * Y i) := by
            simp only [Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro i _; ring
          rw [this, hsum, mul_one, show ∑ i ∈ s, w i * Y i = a from rfl, sub_self, mul_zero]
        have hsplit : ∑ i ∈ s, w i * Fa_fun a (Y i)
            = (∑ i ∈ s, w i * ((39 / 100 : ℝ) * Y i * (h a / a)))
              + (∑ i ∈ s, w i * ((7 / 10000 : ℝ) * (a - Y i)))
              - (∑ i ∈ s, w i * ((Y i + 39 / 100 - a) * h (Y i)))
              + (13 / 25 : ℝ) * (∑ i ∈ s, w i * R_fun (Y i)) := by
          unfold Fa_fun
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _; ring
        have hpart3 : ∑ i ∈ s, w i * ((Y i + 39 / 100 - a) * h (Y i))
            = (∑ i ∈ s, w i * (Y i - a) * h (Y i)) + (39 / 100 : ℝ) * ∑ i ∈ s, w i * h (Y i) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [hsplit, hpart1, hpart2, hpart3]; ring
      linarith
    · -- Regime 3: High mean via ∑ w_i Ghi(a, Y_i) ≥ 0
      push Not at h2
      have hsum_nn : 0 ≤ ∑ i ∈ s, w i * Ghi_fun a (Y i) :=
        Finset.sum_nonneg fun i hi =>
          mul_nonneg (hw i hi) (cov_hi_Ghi_nonneg h2 ha_lt1 (hY i hi).1 (hY i hi).2)
      have hsum_eq : ∑ i ∈ s, w i * Ghi_fun a (Y i)
          = (39 / 100 : ℝ) * (h a - ∑ i ∈ s, w i * h (Y i))
            - ∑ i ∈ s, w i * (Y i - a) * h (Y i) := by
        have hkl_sum : ∑ i ∈ s, w i * KL_fun (Y i) a = h a - ∑ i ∈ s, w i * h (Y i) := by
          have : ∑ i ∈ s, w i * KL_fun (Y i) a
              = (∑ i ∈ s, w i * (h a + (Y i - a) * hp a - h (Y i))) :=
            Finset.sum_congr rfl fun i _ => by rw [KL_eq_tangent ha_pos ha_lt1]
          rw [this]
          have hlin : ∑ i ∈ s, w i * (h a + (Y i - a) * hp a - h (Y i))
              = h a * (∑ i ∈ s, w i) + hp a * ((∑ i ∈ s, w i * Y i) - a * (∑ i ∈ s, w i))
                - ∑ i ∈ s, w i * h (Y i) := by
            simp only [Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro i _; ring
          rw [hlin, hsum, mul_one, mul_one, show ∑ i ∈ s, w i * Y i = a from rfl, sub_self, mul_zero, add_zero]
        have hcov_sum : ∑ i ∈ s, w i * ((a - Y i) * (h a - h (Y i)))
            = ∑ i ∈ s, w i * (Y i - a) * h (Y i) := by
          have hdiff : ∑ i ∈ s, w i * ((a - Y i) * (h a - h (Y i)))
              - ∑ i ∈ s, w i * (Y i - a) * h (Y i)
              = h a * (a * (∑ i ∈ s, w i) - ∑ i ∈ s, w i * Y i) := by
            simp only [Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro i _; ring
          rw [hsum, mul_one, show ∑ i ∈ s, w i * Y i = a from rfl, sub_self, mul_zero] at hdiff
          linarith
        have hsplit : ∑ i ∈ s, w i * Ghi_fun a (Y i)
            = (39 / 100 : ℝ) * (∑ i ∈ s, w i * KL_fun (Y i) a)
              - ∑ i ∈ s, w i * ((a - Y i) * (h a - h (Y i))) := by
          unfold Ghi_fun
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [hsplit, hkl_sum, hcov_sum]
      linarith

end UCBound.Cert2D
