module

public import UCBound.CertConst

@[expose] public section

/-!
# Analytic Bounds, Exact Derivatives, and Interval Derivative Evaluators

Reusable foundation for `Cert1D.lean` and `Cert2D.lean`:
1. Pure-calculus bounds on `B(x, y) = h(x y) - y h(x) - x h(y)`:
   - `B_ge_x_om_y_log`: `x (1 - y) log(1 - y) ≤ B(x, y)`
   - `B_ge_neg_two_L_sqrt`: `-2 L √((1 - x)(1 - y)) ≤ B(x, y)`
   - `cert_R_le_phi`: `R_fun x ≤ phi x` (pure concavity, zero interval arithmetic)
2. Exact 1st and 2nd derivatives of `I_fun x x`, `phi`, `R_fun`, `v_fun`, `b_fun`,
   exact contact derivatives at `rStar`, and certified 50-bit interval derivative evaluators.
3. Generic 1D double-zero convexity lemma `nonneg_of_deriv2_nonneg` and 1D centered-form
   verifier `centered1DPos` + `centered1DPos_sound`.
4. Elementary endpoint bounds on `h(x)` and `phi(x)` near `0` and `1`, plus the analytic
   reduction `bopp2D_of_bopp1D`.
-/

namespace UCBound.Cert

open UCBound UCBound.Iv

/-! ### Generic 1D Double-Zero Convexity Lemma -/

/-- If `f` has a double zero at `r ∈ [a, b]` (`f r = 0`, `f' r = 0`) and `f'' ≥ 0` on `(a, b)`,
    then `0 ≤ f x` for all `x ∈ [a, b]`. -/
lemma nonneg_of_deriv2_nonneg {f f' f'' : ℝ → ℝ} {a b r : ℝ}
    (har : a ≤ r) (hrb : r ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf'_cont : ContinuousOn f' (Set.Icc a b))
    (hf'_deriv : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x ∈ Set.Ioo a b, 0 ≤ f'' x)
    (hfr : f r = 0) (hf'r : f' r = 0) :
    ∀ x ∈ Set.Icc a b, 0 ≤ f x := by
  have hf'_mono : MonotoneOn f' (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hf'_cont
    · intro x hx; rw [interior_Icc] at hx
      exact (hf'_deriv x hx).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Icc] at hx
      rw [(hf'_deriv x hx).deriv]; exact hf'' x hx
  intro x hx
  rcases le_total x r with hxr | hrx
  · have hanti : AntitoneOn f (Set.Icc a r) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc a r) (hf_cont.mono (Set.Icc_subset_Icc_right hrb))
      · intro u hu; rw [interior_Icc] at hu
        exact (hf_deriv u ⟨hu.1, lt_of_lt_of_le hu.2 hrb⟩).differentiableAt.differentiableWithinAt
      · intro u hu; rw [interior_Icc] at hu
        rw [(hf_deriv u ⟨hu.1, lt_of_lt_of_le hu.2 hrb⟩).deriv]
        have := hf'_mono ⟨le_of_lt hu.1, le_trans (le_of_lt hu.2) hrb⟩ ⟨har, hrb⟩ (le_of_lt hu.2)
        linarith
    have := hanti ⟨hx.1, hxr⟩ ⟨har, le_rfl⟩ hxr
    linarith
  · have hmono : MonotoneOn f (Set.Icc r b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc r b) (hf_cont.mono (Set.Icc_subset_Icc_left har))
      · intro u hu; rw [interior_Icc] at hu
        exact (hf_deriv u ⟨lt_of_le_of_lt har hu.1, hu.2⟩).differentiableAt.differentiableWithinAt
      · intro u hu; rw [interior_Icc] at hu
        rw [(hf_deriv u ⟨lt_of_le_of_lt har hu.1, hu.2⟩).deriv]
        have := hf'_mono ⟨har, hrb⟩ ⟨le_trans har (le_of_lt hu.1), le_of_lt hu.2⟩ (le_of_lt hu.1)
        linarith
    have := hmono ⟨le_rfl, hrb⟩ ⟨hrx, hx.2⟩ hrx
    linarith

/-! ### Contact Identities `I_fun rStar rStar = 1/2` and `phi rStar = 1` -/

lemma I_fun_rStar_rStar : I_fun rStar rStar = 1 / 2 := by
  unfold I_fun tau
  have hr_ne : rStar ≠ 0 := ne_of_gt rStar_pos
  have h1r_ne : 1 - rStar ≠ 0 := ne_of_gt (by linarith [rStar_lt_one])
  field_simp [hr_ne, h1r_ne]; ring

lemma phi_rStar : phi rStar = 1 := by
  unfold phi
  rw [I_fun_rStar_rStar, h_half, div_self (ne_of_gt L_pos), Real.sqrt_one]

/-! ### Pure-Calculus `B(x, y) = h(x y) - y h(x) - x h(y)` Lower Bounds -/

/-- Exact cancellation identity for `B(x, y)` on `(0, 1)²`. -/
lemma B_eq_cancel {x y : ℝ} (hx0 : 0 < x) (hy0 : 0 < y) :
    h (x * y) - y * h x - x * h y
      = -(1 - x * y) * Real.log (1 - x * y) + y * (1 - x) * Real.log (1 - x)
        + x * (1 - y) * Real.log (1 - y) := by
  unfold h
  rw [Real.log_mul (ne_of_gt hx0) (ne_of_gt hy0)]
  ring

/-- `B(x, y) ≥ x (1 - y) log(1 - y)` for all `x ∈ [0, 1]` and `y ∈ [0, 1]`. -/
lemma B_ge_x_om_y_log {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    x * (1 - y) * Real.log (1 - y) ≤ h (x * y) - y * h x - x * h y := by
  rcases hx0.eq_or_lt with rfl | hx_pos
  · simp [h_zero]
  rcases hy0.eq_or_lt with rfl | hy_pos
  · simp [h_zero]
  rcases hy1.eq_or_lt with rfl | hy_lt
  · simp [h_one]
  rcases hx1.eq_or_lt with rfl | hx_lt
  · simp only [one_mul, h_one, mul_zero, sub_zero, sub_self]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (Real.log_nonpos (by linarith) (by linarith))
  rw [B_eq_cancel hx_pos hy_pos]
  set g : ℝ → ℝ := fun t => -(1 - x * t) * Real.log (1 - x * t) + t * (1 - x) * Real.log (1 - x)
  set g' : ℝ → ℝ := fun t => x * Real.log (1 - x * t) + x + (1 - x) * Real.log (1 - x)
  have hg_cont : ContinuousOn g (Set.Icc 0 1) := by
    have h1 : Continuous (fun t : ℝ => -((1 - x * t) * Real.log (1 - x * t))) :=
      (Real.continuous_mul_log.comp (continuous_const.sub (continuous_const.mul continuous_id))).neg
    have h2 : Continuous (fun t : ℝ => t * (1 - x) * Real.log (1 - x)) := by fun_prop
    have heq : g = fun t => -((1 - x * t) * Real.log (1 - x * t)) + t * (1 - x) * Real.log (1 - x) := by
      ext t; simp only [g]; ring
    rw [heq]; exact (h1.add h2).continuousOn
  have hg_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ht
    have h1mxt : 0 < 1 - x * t := by nlinarith [ht.1, ht.2]
    have ha : HasDerivAt (fun u : ℝ => 1 - x * u) (-x) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub ((hasDerivAt_id' t).const_mul x)
    have hb : HasDerivAt (fun u : ℝ => Real.log (1 - x * u)) ((-x) / (1 - x * t)) t :=
      ha.log (ne_of_gt h1mxt)
    have hprod : HasDerivAt (fun u : ℝ => -(1 - x * u) * Real.log (1 - x * u))
        (-(-x) * Real.log (1 - x * t) + -(1 - x * t) * ((-x) / (1 - x * t))) t :=
      (ha.fun_neg).fun_mul hb
    have hlin : HasDerivAt (fun u : ℝ => u * (1 - x) * Real.log (1 - x)) ((1 - x) * Real.log (1 - x)) t := by
      have := ((hasDerivAt_id' t).mul_const (1 - x)).mul_const (Real.log (1 - x))
      simpa using this
    exact (hprod.fun_add hlin).congr_deriv (by simp only [g']; field_simp [ne_of_gt h1mxt])
  have hg'_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g' (-(x ^ 2 / (1 - x * t))) t := by
    intro t ht
    have h1mxt : 0 < 1 - x * t := by nlinarith [ht.1, ht.2]
    have ha : HasDerivAt (fun u : ℝ => 1 - x * u) (-x) t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub ((hasDerivAt_id' t).const_mul x)
    have hb : HasDerivAt (fun u : ℝ => Real.log (1 - x * u)) ((-x) / (1 - x * t)) t :=
      ha.log (ne_of_gt h1mxt)
    have h1 := ((hb.const_mul x).add_const x).add_const ((1 - x) * Real.log (1 - x))
    exact h1.congr_deriv (by field_simp [ne_of_gt h1mxt])
  have hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g := by
    apply concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hg_cont
    · intro t ht; rw [interior_Icc] at ht
      exact (hg_deriv t ht).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc] at ht
      have hdeq : deriv g =ᶠ[nhds t] g' := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu; exact (hg_deriv u hu).deriv
      exact ((hg'_deriv t ht).congr_of_eventuallyEq hdeq).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc] at ht
      have hdeq : deriv g =ᶠ[nhds t] g' := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu; exact (hg_deriv u hu).deriv
      have h2 := ((hg'_deriv t ht).congr_of_eventuallyEq hdeq).deriv
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      rw [h2]
      have h1mxt : 0 < 1 - x * t := by nlinarith [ht.1, ht.2]
      linarith [div_nonneg (sq_nonneg x) (le_of_lt h1mxt)]
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 = 0 := by simp [g]; ring
  have hmem := hconc.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) (show 0 ≤ 1 - y by linarith) (le_of_lt hy_pos) (by ring)
  have hmid : (1 - y) * (0 : ℝ) + y * 1 = y := by ring
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hmid, hg0, hg1] at hmem
  have hgy : 0 ≤ g y := by linarith
  dsimp only [g] at hgy
  linarith

/-- Symmetric version: `B(x, y) ≥ y (1 - x) log(1 - x)`. -/
lemma B_ge_y_om_x_log {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    y * (1 - x) * Real.log (1 - x) ≤ h (x * y) - y * h x - x * h y := by
  have := B_ge_x_om_y_log hy0 hy1 hx0 hx1
  rw [mul_comm y x] at this; linarith

/-- Pure-calculus bound `B(x, y) ≥ -2 L √((1 - x)(1 - y))` for all `x, y ∈ [0, 1]`. -/
lemma B_ge_neg_two_L_sqrt {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    -2 * L * Real.sqrt ((1 - x) * (1 - y)) ≤ h (x * y) - y * h x - x * h y := by
  have hL := le_of_lt L_pos
  rcases hx0.eq_or_lt with rfl | hx_pos
  · simp [h_zero]; positivity
  rcases hy0.eq_or_lt with rfl | hy_pos
  · simp [h_zero]; positivity
  rcases hx1.eq_or_lt with rfl | hx_lt
  · simp [h_one]
  rcases hy1.eq_or_lt with rfl | hy_lt
  · simp [h_one]
  set a := 1 - x
  set b := 1 - y
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  set P := 1 - x * y
  have hP_gt_a : a < P := by nlinarith
  have hP_pos : 0 < P := lt_trans ha0 hP_gt_a
  have hP_le : P ≤ a + b := by nlinarith
  have hPma : P - a = b * x := by simp only [P, a, b]; ring
  have hid : P * h (a / P) + (h (x * y) - y * h x - x * h y) = b * h x := by
    rw [B_eq_cancel hx_pos hy_pos]
    unfold h
    have h1maP : 1 - a / P = b * x / P := by
      field_simp [ne_of_gt hP_pos]; linarith [hPma]
    rw [h1maP, Real.log_div (ne_of_gt ha0) (ne_of_gt hP_pos),
        Real.log_div (ne_of_gt (mul_pos hb0 hx_pos)) (ne_of_gt hP_pos),
        Real.log_mul (ne_of_gt hb0) (ne_of_gt hx_pos)]
    have ha_eq : 1 - x = a := rfl
    have hb_eq : 1 - y = b := rfl
    have hP_eq' : 1 - x * y = P := rfl
    rw [ha_eq, hb_eq, hP_eq']
    field_simp [ne_of_gt hP_pos]
    have : P - a - b * x = 0 := by linarith [hPma]
    have : y = 1 - b := by simp only [b]; ring
    nlinarith
  have hmono : P * h (a / P) ≤ (a + b) * h (a / (a + b)) := by
    set φ : ℝ → ℝ := fun u => u * h (a / u)
    have hφ_deriv : ∀ u ∈ Set.Icc P (a + b), HasDerivAt φ (-Real.log (1 - a / u)) u := by
      intro u hu
      have hu_gt_a : a < u := lt_of_lt_of_le hP_gt_a hu.1
      have hu_pos : 0 < u := lt_trans ha0 hu_gt_a
      have hau0 : 0 < a / u := div_pos ha0 hu_pos
      have hau1 : a / u < 1 := (div_lt_one hu_pos).mpr hu_gt_a
      have hd_div : HasDerivAt (fun t : ℝ => a / t) (-(a / u ^ 2)) u := by
        have := (hasDerivAt_const u a).fun_div (hasDerivAt_id' u) (ne_of_gt hu_pos)
        exact this.congr_deriv (by ring)
      have hd_h : HasDerivAt (fun t : ℝ => h (a / t)) (hp (a / u) * (-(a / u ^ 2))) u :=
        (hasDerivAt_h hau0 hau1).comp u hd_div
      have hd_mul := (hasDerivAt_id' u).fun_mul hd_h
      exact hd_mul.congr_deriv (by
        unfold h hp
        have h1mau : 0 < 1 - a / u := by linarith
        rw [Real.log_div (ne_of_gt h1mau) (ne_of_gt hau0)]
        field_simp [ne_of_gt hu_pos]; ring)
    have hmon : MonotoneOn φ (Set.Icc P (a + b)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc P (a + b))
      · intro u hu; exact (hφ_deriv u hu).continuousAt.continuousWithinAt
      · intro u hu; rw [interior_Icc] at hu
        exact (hφ_deriv u (Set.Ioo_subset_Icc_self hu)).differentiableAt.differentiableWithinAt
      · intro u hu; rw [interior_Icc] at hu
        rw [(hφ_deriv u (Set.Ioo_subset_Icc_self hu)).deriv]
        have hu_gt_a : a < u := lt_of_lt_of_le hP_gt_a (le_of_lt hu.1)
        have hu_pos : 0 < u := lt_trans ha0 hu_gt_a
        have h1 : 1 - a / u ≤ 1 := by linarith [div_pos ha0 hu_pos]
        have h2 : 0 < 1 - a / u := by rw [sub_pos, div_lt_one hu_pos]; exact hu_gt_a
        linarith [Real.log_nonpos (le_of_lt h2) h1]
    exact hmon ⟨le_rfl, hP_le⟩ ⟨hP_le, le_rfl⟩ hP_le
  have hab_pos : 0 < a + b := by linarith
  have ht0 : 0 ≤ a / (a + b) := div_nonneg (le_of_lt ha0) (le_of_lt hab_pos)
  have ht1 : a / (a + b) ≤ 1 := (div_le_one hab_pos).mpr (by linarith)
  have hsqrt := h_le_two_L_sqrt ht0 ht1
  have hsimp : (a + b) * Real.sqrt (a / (a + b) * (1 - a / (a + b))) = Real.sqrt (a * b) := by
    have h1 : a / (a + b) * (1 - a / (a + b)) = (a * b) / (a + b) ^ 2 := by
      field_simp [ne_of_gt hab_pos]; ring
    rw [h1, Real.sqrt_div (mul_nonneg (le_of_lt ha0) (le_of_lt hb0)),
        Real.sqrt_sq (le_of_lt hab_pos)]
    field_simp [ne_of_gt hab_pos]
  have hstep3 : (a + b) * h (a / (a + b)) ≤ 2 * L * Real.sqrt (a * b) := by
    calc (a + b) * h (a / (a + b))
        ≤ (a + b) * (2 * L * Real.sqrt (a / (a + b) * (1 - a / (a + b)))) :=
          mul_le_mul_of_nonneg_left hsqrt (le_of_lt hab_pos)
      _ = 2 * L * ((a + b) * Real.sqrt (a / (a + b) * (1 - a / (a + b)))) := by ring
      _ = 2 * L * Real.sqrt (a * b) := by rw [hsimp]
  have hbh_nn : 0 ≤ b * h x := mul_nonneg (le_of_lt hb0) (h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt))
  linarith

/-- Pure-analytic proof of `R_fun x ≤ phi x` on `[0, 1]` (zero interval arithmetic!). -/
theorem cert_R_le_phi : ∀ x, 0 ≤ x → x ≤ 1 → R_fun x ≤ phi x := by
  intro x hx0 hx1
  have hq_pos : 0 < qStar := pos_of_lo_pos validConstIv.hq_mem (by decide)
  have hqL_pos : 0 < qStar * L := mul_pos hq_pos L_pos
  have hB_nonpos : h (rStar * x) - x * hr - rStar * h x ≤ 0 := by
    rcases hx0.eq_or_lt with rfl | hx_pos
    · simp [h_zero]
    rcases hx1.eq_or_lt with rfl | hx_lt
    · simp [h_one, hr]
    set g : ℝ → ℝ := fun t => rStar * h t + t * hr - h (rStar * t)
    set g' : ℝ → ℝ := fun t => rStar * hp t + hr - rStar * hp (rStar * t)
    have hr0 := rStar_pos; have hr1 := rStar_lt_one
    have hg_cont : ContinuousOn g (Set.Icc 0 1) := by
      have h1 : ContinuousOn (fun t : ℝ => rStar * h t + t * hr) (Set.Icc 0 1) :=
        (continuousOn_const.mul continuousOn_h).add (continuousOn_id.mul continuousOn_const)
      have h2 : ContinuousOn (fun t : ℝ => h (rStar * t)) (Set.Icc 0 1) :=
        continuousOn_h.comp (continuousOn_const.mul continuousOn_id)
          (fun t ht => ⟨mul_nonneg (le_of_lt hr0) ht.1, by nlinarith [ht.1, ht.2]⟩)
      exact h1.sub h2
    have hg_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (g' t) t := by
      intro t ht
      have hrt0 : 0 < rStar * t := mul_pos hr0 ht.1
      have hrt1 : rStar * t < 1 := by nlinarith [ht.1, ht.2]
      have h1 := ((hasDerivAt_h ht.1 ht.2).const_mul rStar).fun_add ((hasDerivAt_id' t).mul_const hr)
      have h2 : HasDerivAt (fun u : ℝ => h (rStar * u)) (hp (rStar * t) * rStar) t := by
        simpa [Function.comp_def] using (hasDerivAt_h hrt0 hrt1).comp t ((hasDerivAt_id' t).const_mul rStar)
      exact (h1.fun_sub h2).congr_deriv (by simp only [g']; ring)
    have hg'_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt g' (-(rStar * (1 - rStar) / ((1 - t) * (1 - rStar * t)))) t := by
      intro t ht
      have hrt0 : 0 < rStar * t := mul_pos hr0 ht.1
      have hrt1 : rStar * t < 1 := by nlinarith [ht.1, ht.2]
      have h1 : HasDerivAt (fun u : ℝ => rStar * hp u + hr) (rStar * -(1 / (t * (1 - t)))) t :=
        ((hasDerivAt_hp ht.1 ht.2).const_mul rStar).add_const hr
      have h2 : HasDerivAt (fun u : ℝ => rStar * hp (rStar * u))
          (rStar * (-(1 / (rStar * t * (1 - rStar * t))) * rStar)) t := by
        have hcomp : HasDerivAt (fun u : ℝ => hp (rStar * u)) (-(1 / (rStar * t * (1 - rStar * t))) * rStar) t := by
          simpa [Function.comp_def] using (hasDerivAt_hp hrt0 hrt1).comp t ((hasDerivAt_id' t).const_mul rStar)
        exact hcomp.const_mul rStar
      have hsub := h1.fun_sub h2
      have hfun : g' = fun u => (rStar * hp u + hr) - rStar * hp (rStar * u) := rfl
      rw [hfun]
      exact hsub.congr_deriv (by
        have ht_ne : t ≠ 0 := ne_of_gt ht.1
        have h1t_ne : 1 - t ≠ 0 := ne_of_gt (by linarith [ht.2])
        have h1rt_ne : 1 - rStar * t ≠ 0 := ne_of_gt (by linarith)
        have hr_ne : rStar ≠ 0 := ne_of_gt hr0
        field_simp [ht_ne, h1t_ne, h1rt_ne, hr_ne]; ring)
    have hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g := by
      apply concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hg_cont
      · intro t ht; rw [interior_Icc] at ht
        exact (hg_deriv t ht).differentiableAt.differentiableWithinAt
      · intro t ht; rw [interior_Icc] at ht
        have hdeq : deriv g =ᶠ[nhds t] g' := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu; exact (hg_deriv u hu).deriv
        exact ((hg'_deriv t ht).congr_of_eventuallyEq hdeq).differentiableAt.differentiableWithinAt
      · intro t ht; rw [interior_Icc] at ht
        have hdeq : deriv g =ᶠ[nhds t] g' := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu; exact (hg_deriv u hu).deriv
        have h2 := ((hg'_deriv t ht).congr_of_eventuallyEq hdeq).deriv
        simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
        rw [h2]
        have hnum : 0 < rStar * (1 - rStar) := mul_pos hr0 (by linarith)
        have hden : 0 < (1 - t) * (1 - rStar * t) :=
          mul_pos (by linarith [ht.2]) (by nlinarith [ht.1, ht.2])
        linarith [div_pos hnum hden]
    have hg0 : g 0 = 0 := by simp [g, h_zero]
    have hg1 : g 1 = 0 := by simp [g, h_one, hr]
    have hmem := hconc.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) (show 0 ≤ 1 - x by linarith) (le_of_lt hx_pos) (by ring)
    have hmid : (1 - x) * (0 : ℝ) + x * 1 = x := by ring
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hmid, hg0, hg1] at hmem
    dsimp only [g] at hmem; linarith
  unfold R_fun F_fun
  rw [phi_rStar, mul_one, div_le_iff₀ hqL_pos]
  unfold hr at hB_nonpos
  linarith

/-! ### Exact 1st & 2nd Derivatives of `I_fun x x`, `phi`, `R_fun`, `v_fun`, `b_fun` -/

noncomputable def hpp (x : ℝ) : ℝ := -(1 / (x * (1 - x)))
noncomputable def IxxP (x : ℝ) : ℝ := 2 * x * (1 + tau * (1 - x) * (1 - 2 * x))
noncomputable def IxxPP (x : ℝ) : ℝ := 2 + 2 * tau * (1 - 6 * x + 6 * x ^ 2)
noncomputable def phiP (x : ℝ) : ℝ := IxxP x * hp (I_fun x x) / (2 * L * phi x)
noncomputable def phiPP (x : ℝ) : ℝ :=
  (IxxPP x * hp (I_fun x x) + (IxxP x) ^ 2 * hpp (I_fun x x) - 2 * L * (phiP x) ^ 2) / (2 * L * phi x)
noncomputable def RP (x : ℝ) : ℝ := (rStar * (hp (rStar * x) - hp x) - hr) / (qStar * L) + phiP x
noncomputable def RPP (x : ℝ) : ℝ := (rStar ^ 2 * hpp (rStar * x) - rStar * hpp x) / (qStar * L) + phiPP x
noncomputable def vP (x : ℝ) : ℝ := hp x - hr * phiP x
noncomputable def vPP (x : ℝ) : ℝ := hpp x - hr * phiPP x
noncomputable def bP (x : ℝ) : ℝ := 1 - hp x / pStar - cParam * phiP x
noncomputable def bPP (x : ℝ) : ℝ := -(hpp x / pStar) - cParam * phiPP x

lemma I_fun_self_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < I_fun x x := by
  unfold I_fun
  have : 0 < 1 + tau * (1 - x) * (1 - x) := by
    have := tau_pos; nlinarith [sq_nonneg (1 - x)]
  nlinarith [sq_pos_of_pos hx0]

lemma I_fun_self_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : I_fun x x < 1 := by
  unfold I_fun
  have ht := tau_lt_half
  have h1 : 1 + tau * (1 - x) * (1 - x) ≤ 1 + (1 / 2) * (1 - x) ^ 2 := by
    nlinarith [sq_nonneg (1 - x)]
  have h2 : x * x * (1 + (1 / 2) * (1 - x) ^ 2) < 1 := by
    have : 1 - x * x * (1 + (1 / 2) * (1 - x) ^ 2)
        = (1 - x) * (1 + x - (1 / 2) * x ^ 2 * (1 - x)) := by ring
    have hfac : 0 < 1 + x - (1 / 2) * x ^ 2 * (1 - x) := by nlinarith [sq_nonneg x]
    nlinarith
  nlinarith [sq_pos_of_pos hx0]

lemma phi_pos_of_Ioo {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < phi x := by
  unfold phi
  exact Real.sqrt_pos.mpr (div_pos (h_pos (I_fun_self_pos hx0 hx1) (I_fun_self_lt_one hx0 hx1)) L_pos)

lemma hasDerivAt_Ixx (x : ℝ) : HasDerivAt (fun t => I_fun t t) (IxxP x) x := by
  have h1 : HasDerivAt (fun t : ℝ => t * t) (1 * x + x * 1) x :=
    (hasDerivAt_id' x).fun_mul (hasDerivAt_id' x)
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x)
  have h3 := h2.fun_mul h2
  have h4 := (hasDerivAt_const x (1 : ℝ)).fun_add (h3.const_mul tau)
  have hfun : (fun t => I_fun t t) = fun t => (t * t) * (1 + tau * ((1 - t) * (1 - t))) := by
    ext t; unfold I_fun; ring
  rw [hfun]; exact (h1.fun_mul h4).congr_deriv (by unfold IxxP; ring)

lemma hasDerivAt_IxxP (x : ℝ) : HasDerivAt IxxP (IxxPP x) x := by
  have hfun : IxxP = fun t => 2 * t + 2 * tau * (t - 3 * t ^ 2 + 2 * t ^ 3) := by
    ext t; unfold IxxP; ring
  rw [hfun]
  have hd1 : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by simpa using (hasDerivAt_id' x).const_mul 2
  have hd2 : HasDerivAt (fun t : ℝ => t - 3 * t ^ 2 + 2 * t ^ 3) (1 - 6 * x + 6 * x ^ 2) x := by
    have ha := hasDerivAt_id' x
    have hb := (hasDerivAt_pow 2 x).const_mul 3
    have hc := (hasDerivAt_pow 3 x).const_mul 2
    exact ((ha.fun_sub hb).fun_add hc).congr_deriv (by ring)
  exact (hd1.fun_add (hd2.const_mul (2 * tau))).congr_deriv (by unfold IxxPP; ring)

lemma hasDerivAt_phi {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt phi (phiP x) x := by
  have hI0 := I_fun_self_pos hx0 hx1
  have hI1 := I_fun_self_lt_one hx0 hx1
  have hh_pos : 0 < h (I_fun x x) / L := div_pos (h_pos hI0 hI1) L_pos
  have hd_h : HasDerivAt (fun t => h (I_fun t t)) (hp (I_fun x x) * IxxP x) x := by
    exact HasDerivAt.comp (h := fun t => I_fun t t) x (hasDerivAt_h hI0 hI1) (hasDerivAt_Ixx x)
  have hd_sq : HasDerivAt (fun t => Real.sqrt (h (I_fun t t) / L))
      ((hp (I_fun x x) * IxxP x / L) / (2 * Real.sqrt (h (I_fun x x) / L))) x :=
    (hd_h.div_const L).sqrt (ne_of_gt hh_pos)
  exact hd_sq.congr_deriv (by
    unfold phiP phi
    have hphi_ne : Real.sqrt (h (I_fun x x) / L) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hh_pos)
    field_simp [ne_of_gt L_pos, hphi_ne])

lemma hasDerivAt_phiP {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt phiP (phiPP x) x := by
  have hI0 := I_fun_self_pos hx0 hx1
  have hI1 := I_fun_self_lt_one hx0 hx1
  have hphi_pos := phi_pos_of_Ioo hx0 hx1
  have hL_ne : L ≠ 0 := ne_of_gt L_pos
  have hphi_ne : phi x ≠ 0 := ne_of_gt hphi_pos
  have hden_ne : 2 * L * phi x ≠ 0 := ne_of_gt (mul_pos (mul_pos two_pos L_pos) hphi_pos)
  have hd_hp : HasDerivAt (fun t => hp (I_fun t t)) (hpp (I_fun x x) * IxxP x) x := by
    exact HasDerivAt.comp (h := fun t => I_fun t t) x (hasDerivAt_hp hI0 hI1) (hasDerivAt_Ixx x)
  have hd_num : HasDerivAt (fun t => IxxP t * hp (I_fun t t))
      (IxxPP x * hp (I_fun x x) + IxxP x * (hpp (I_fun x x) * IxxP x)) x :=
    (hasDerivAt_IxxP x).fun_mul hd_hp
  have hd_den : HasDerivAt (fun t => 2 * L * phi t) (2 * L * phiP x) x :=
    (hasDerivAt_phi hx0 hx1).const_mul (2 * L)
  have hd_q : HasDerivAt (fun t => IxxP t * hp (I_fun t t) / (2 * L * phi t)) _ x :=
    hd_num.fun_div hd_den hden_ne
  exact hd_q.congr_deriv (by unfold phiPP phiP; field_simp [hL_ne, hphi_ne])

lemma hasDerivAt_R {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt R_fun (RP x) x := by
  have hr0 := rStar_pos; have hr1 := rStar_lt_one
  have hrx0 : 0 < rStar * x := mul_pos hr0 hx0
  have hrx1 : rStar * x < 1 := by nlinarith
  have hfun : R_fun = fun t => (h (rStar * t) - t * hr - rStar * h t) / (qStar * L) + phi t := by
    ext t; unfold R_fun F_fun hr
    rw [phi_rStar, mul_one]
    have hq_ne : qStar ≠ 0 := ne_of_gt (pos_of_lo_pos validConstIv.hq_mem (by decide))
    have hL_ne : L ≠ 0 := ne_of_gt L_pos
    field_simp [hq_ne, hL_ne]; ring
  rw [hfun]
  have hd1 : HasDerivAt (fun t => h (rStar * t)) (hp (rStar * x) * rStar) x := by
    simpa [Function.comp_def] using (hasDerivAt_h hrx0 hrx1).comp x ((hasDerivAt_id' x).const_mul rStar)
  have hd2 := (hasDerivAt_id' x).mul_const hr
  have hd3 := (hasDerivAt_h hx0 hx1).const_mul rStar
  have hd_q := ((hd1.fun_sub hd2).fun_sub hd3).div_const (qStar * L)
  exact (hd_q.fun_add (hasDerivAt_phi hx0 hx1)).congr_deriv (by unfold RP; ring)

lemma hasDerivAt_RP {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt RP (RPP x) x := by
  have hr0 := rStar_pos; have hr1 := rStar_lt_one
  have hrx0 : 0 < rStar * x := mul_pos hr0 hx0
  have hrx1 : rStar * x < 1 := by nlinarith
  have hd1 : HasDerivAt (fun t => hp (rStar * t)) (hpp (rStar * x) * rStar) x := by
    simpa [Function.comp_def, hpp] using (hasDerivAt_hp hrx0 hrx1).comp x ((hasDerivAt_id' x).const_mul rStar)
  have hd2 : HasDerivAt hp (hpp x) x := hasDerivAt_hp hx0 hx1
  have hd_num := ((hd1.fun_sub hd2).const_mul rStar).sub_const hr
  have hd_q := hd_num.div_const (qStar * L)
  have hd_tot : HasDerivAt (fun t => (rStar * (hp (rStar * t) - hp t) - hr) / (qStar * L) + phiP t) _ x :=
    hd_q.fun_add (hasDerivAt_phiP hx0 hx1)
  exact hd_tot.congr_deriv (by unfold RPP; ring)

lemma hasDerivAt_v {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt v_fun (vP x) x :=
  (hasDerivAt_h hx0 hx1).fun_sub ((hasDerivAt_phi hx0 hx1).const_mul hr)

lemma hasDerivAt_vP {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt vP (vPP x) x :=
  (hasDerivAt_hp hx0 hx1).fun_sub ((hasDerivAt_phiP hx0 hx1).const_mul hr)

lemma hasDerivAt_b {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt b_fun (bP x) x :=
  ((hasDerivAt_id' x).fun_sub ((hasDerivAt_h hx0 hx1).div_const pStar)).fun_sub
    ((hasDerivAt_phi hx0 hx1).const_mul cParam)

lemma hasDerivAt_bP {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt bP (bPP x) x := by
  have h1 : HasDerivAt (fun t => 1 - hp t / pStar) (-(hpp x / pStar)) x := by
    have := (hasDerivAt_const x (1 : ℝ)).fun_sub ((hasDerivAt_hp hx0 hx1).div_const pStar)
    exact this.congr_deriv (by unfold hpp; ring)
  exact h1.fun_sub ((hasDerivAt_phiP hx0 hx1).const_mul cParam)

/-- Exact contact values and derivatives at `rStar`. -/
lemma contact_derivs :
    phiP rStar = 0 ∧
    R_fun rStar = 0 ∧ RP rStar = 0 ∧
    v_fun rStar = 0 ∧ vP rStar = pStar ∧
    b_fun rStar = 0 ∧ bP rStar = 0 := by
  have hhp_half : hp (1 / 2) = 0 := by unfold hp; norm_num
  have hphiP : phiP rStar = 0 := by unfold phiP; rw [I_fun_rStar_rStar, hhp_half, mul_zero, zero_div]
  have hR0 : R_fun rStar = 0 := by
    unfold R_fun F_fun
    rw [phi_rStar, mul_one, mul_one]
    have hci := contact_identity
    have hsq : rStar * rStar = rStar ^ 2 := by ring
    rw [hsq]
    unfold hr at hci
    have hnum : h (rStar ^ 2) + qStar * L - rStar * h rStar - rStar * h rStar = 0 := by linarith
    rw [hnum, zero_div]
  have hRP0 : RP rStar = 0 := by
    unfold RP; rw [hphiP, add_zero]
    have hnum : rStar * (hp (rStar * rStar) - hp rStar) - hr = 0 := by
      have hr0 := rStar_pos; have hr1 := rStar_lt_one
      have h1r : 0 < 1 - rStar := by linarith
      have h1pr : 0 < 1 + rStar := by linarith
      have hfac : (1 - rStar * rStar) / (rStar * rStar) = ((1 - rStar) / rStar) * ((1 + rStar) / rStar) := by
        field_simp [ne_of_gt hr0]; ring
      unfold hp hr h
      rw [hfac, Real.log_mul (ne_of_gt (div_pos h1r hr0)) (ne_of_gt (div_pos h1pr hr0)),
          Real.log_div (ne_of_gt h1pr) (ne_of_gt hr0)]
      have hreq := rootEq_rStar
      unfold rootEq at hreq
      linarith
    rw [hnum, zero_div]
  have hv0 : v_fun rStar = 0 := by unfold v_fun; rw [phi_rStar, mul_one]; unfold hr; ring
  have hvP : vP rStar = pStar := by unfold vP pStar; rw [hphiP, mul_zero, sub_zero]
  have hb0 : b_fun rStar = 0 := by unfold b_fun cParam hr; rw [phi_rStar, mul_one]; ring
  have hbP : bP rStar = 0 := by
    unfold bP; rw [hphiP, mul_zero, sub_zero]
    have hp_eq : hp rStar = pStar := rfl
    rw [hp_eq, div_self pStar_ne_zero, sub_self]
  exact ⟨hphiP, hR0, hRP0, hv0, hvP, hb0, hbP⟩

/-! ### Certified 50-bit Interval Evaluators for Derivatives -/

def hppIv (X : Interval) : Interval :=
  neg (invPos (mul X (sub ONE X)))

lemma mem_hppIv {X : Interval} {x : ℝ} (hx : mem X x)
    (hpos : 0 < (mul X (sub ONE X)).lo) : mem (hppIv X) (hpp x) := by
  unfold hppIv hpp
  have h := mem_neg (mem_invPos (mem_mul hx (mem_sub mem_ONE hx)) hpos)
  simpa [one_div] using h

def IxxPIv (X : Interval) : Interval :=
  let omx := sub ONE X
  let t := add ONE (mul constIv.tau (mul omx (sub ONE (mul (ofInt 2) X))))
  mul (mul (ofInt 2) X) t

lemma mem_IxxPIv {X : Interval} {x : ℝ} (hx : mem X x) : mem (IxxPIv X) (IxxP x) := by
  unfold IxxPIv IxxP
  have h := mem_mul (mem_mul (mem_ofInt 2) hx)
    (mem_add mem_ONE (mem_mul validConstIv.htau_mem
      (mem_mul (mem_sub mem_ONE hx) (mem_sub mem_ONE (mem_mul (mem_ofInt 2) hx)))))
  convert h using 1; ring

def IxxPPIv (X : Interval) : Interval :=
  let poly := add (sub ONE (mul (ofInt 6) X)) (mul (ofInt 6) (sq X))
  add (ofInt 2) (mul (ofInt 2) (mul constIv.tau poly))

lemma mem_IxxPPIv {X : Interval} {x : ℝ} (hx : mem X x) : mem (IxxPPIv X) (IxxPP x) := by
  unfold IxxPPIv IxxPP
  have h := mem_add (mem_ofInt 2) (mem_mul (mem_ofInt 2) (mem_mul validConstIv.htau_mem
    (mem_add (mem_sub mem_ONE (mem_mul (mem_ofInt 6) hx)) (mem_mul (mem_ofInt 6) (mem_sq hx)))))
  convert h using 1; ring

def phiPIv (X : Interval) : Interval :=
  let Ix := IxxIv constIv X
  divPos (mul (IxxPIv X) (hpIv Ix)) (mul (mul (ofInt 2) LN2) (phiIv constIv X))

lemma mem_phiPIv {X : Interval} {x : ℝ} (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hI0 : 0 < (IxxIv constIv X).lo) (hI1 : 0 < (sub ONE (IxxIv constIv X)).lo)
    (hden : 0 < (mul (mul (ofInt 2) LN2) (phiIv constIv X)).lo) :
    mem (phiPIv X) (phiP x) := by
  unfold phiPIv phiP
  have hI := mem_IxxIv validConstIv hx hx0 hx1
  have hhp := mem_hpIv hI hI0 hI1
  have hphi := mem_phiIv validConstIv hx hx0 hx1
  have hres := mem_divPos (mem_mul (mem_IxxPIv hx) hhp)
    (mem_mul (mem_mul (mem_ofInt 2) mem_LN2) hphi) hden
  simpa using hres

def phiPPIv (X : Interval) : Interval :=
  let Ix := IxxIv constIv X
  let Ip := IxxPIv X
  let Ipp := IxxPPIv X
  let pp := phiPIv X
  let num := sub (add (mul Ipp (hpIv Ix)) (mul (sq Ip) (hppIv Ix)))
    (mul (mul (ofInt 2) LN2) (sq pp))
  divPos num (mul (mul (ofInt 2) LN2) (phiIv constIv X))

lemma mem_phiPPIv {X : Interval} {x : ℝ} (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hI0 : 0 < (IxxIv constIv X).lo) (hI1 : 0 < (sub ONE (IxxIv constIv X)).lo)
    (hIprod : 0 < (mul (IxxIv constIv X) (sub ONE (IxxIv constIv X))).lo)
    (hden : 0 < (mul (mul (ofInt 2) LN2) (phiIv constIv X)).lo) :
    mem (phiPPIv X) (phiPP x) := by
  unfold phiPPIv phiPP
  have hI := mem_IxxIv validConstIv hx hx0 hx1
  have hhp := mem_hpIv hI hI0 hI1
  have hhpp := mem_hppIv hI hIprod
  have hpp := mem_phiPIv hx hx0 hx1 hI0 hI1 hden
  have hphi := mem_phiIv validConstIv hx hx0 hx1
  have hres := mem_divPos (mem_sub (mem_add (mem_mul (mem_IxxPPIv hx) hhp)
      (mem_mul (mem_sq (mem_IxxPIv hx)) hhpp))
    (mem_mul (mem_mul (mem_ofInt 2) mem_LN2) (mem_sq hpp)))
    (mem_mul (mem_mul (mem_ofInt 2) mem_LN2) hphi) hden
  simpa using hres

def qLIv1 : Interval := ⟨182796046504768, 182796046504801⟩
lemma mem_qLIv1 : mem qLIv1 (qStar * L) := by
  rw [show qLIv1 = mul constIv.q LN2 by decide]; exact mem_mul validConstIv.hq_mem mem_LN2

def RPIv (X : Interval) : Interval :=
  let rx := mul constIv.r X
  let num := sub (mul constIv.r (sub (hpIv rx) (hpIv X))) constIv.hr
  add (divPos num qLIv1) (phiPIv X)

lemma mem_RPIv {X : Interval} {x : ℝ} (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hX0 : 0 < X.lo) (hX1 : 0 < (sub ONE X).lo)
    (hrx0 : 0 < (mul constIv.r X).lo) (hrx1 : 0 < (sub ONE (mul constIv.r X)).lo)
    (hI0 : 0 < (IxxIv constIv X).lo) (hI1 : 0 < (sub ONE (IxxIv constIv X)).lo)
    (hden : 0 < (mul (mul (ofInt 2) LN2) (phiIv constIv X)).lo) :
    mem (RPIv X) (RP x) := by
  unfold RPIv RP
  have hrx := mem_mul validConstIv.hr_mem hx
  exact mem_add (mem_divPos (mem_sub (mem_mul validConstIv.hr_mem
      (mem_sub (mem_hpIv hrx hrx0 hrx1) (mem_hpIv hx hX0 hX1))) validConstIv.hhr_mem)
    mem_qLIv1 (by decide)) (mem_phiPIv hx hx0 hx1 hI0 hI1 hden)

def RPPIv (X : Interval) : Interval :=
  let rx := mul constIv.r X
  let num := sub (mul (sq constIv.r) (hppIv rx)) (mul constIv.r (hppIv X))
  add (divPos num qLIv1) (phiPPIv X)

lemma mem_RPPIv {X : Interval} {x : ℝ} (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hXprod : 0 < (mul X (sub ONE X)).lo)
    (hrxprod : 0 < (mul (mul constIv.r X) (sub ONE (mul constIv.r X))).lo)
    (hI0 : 0 < (IxxIv constIv X).lo) (hI1 : 0 < (sub ONE (IxxIv constIv X)).lo)
    (hIprod : 0 < (mul (IxxIv constIv X) (sub ONE (IxxIv constIv X))).lo)
    (hden : 0 < (mul (mul (ofInt 2) LN2) (phiIv constIv X)).lo) :
    mem (RPPIv X) (RPP x) := by
  unfold RPPIv RPP
  have hrx := mem_mul validConstIv.hr_mem hx
  exact mem_add (mem_divPos (mem_sub (mem_mul (mem_sq validConstIv.hr_mem) (mem_hppIv hrx hrxprod))
      (mem_mul validConstIv.hr_mem (mem_hppIv hx hXprod)))
    mem_qLIv1 (by decide)) (mem_phiPPIv hx hx0 hx1 hI0 hI1 hIprod hden)

def vPIv (X : Interval) : Interval := sub (hpIv X) (mul constIv.hr (phiPIv X))
def vPPIv (X : Interval) : Interval := sub (hppIv X) (mul constIv.hr (phiPPIv X))
def bPIv (X : Interval) : Interval := sub (sub ONE (divNeg (hpIv X) constIv.p)) (mul constIv.c (phiPIv X))
def bPPIv (X : Interval) : Interval := sub (neg (divNeg (hppIv X) constIv.p)) (mul constIv.c (phiPPIv X))

/-! ### Generic 1D Centered-Form Checker -/

def centered1DPos (f fp : Interval → Interval) (X : Interval) : Bool :=
  if 0 < (f X).lo then true
  else
    let m := (X.lo + X.hi) / 2
    let hw := max (m - X.lo) (X.hi - m)
    let fm := f (pt m)
    let M := absHi (fp X)
    decide (0 < (sub fm (mul (pt M) (pt hw))).lo)

lemma centered1DPos_sound {fI fpI : Interval → Interval} {f f' : ℝ → ℝ}
    {X : Interval} (hX : X.lo ≤ X.hi)
    (hfI : ∀ I, X.lo ≤ I.lo → I.hi ≤ X.hi → ∀ u, mem I u → mem (fI I) (f u))
    (hfpI : ∀ u, mem X u → mem (fpI X) (f' u))
    (hcont : ContinuousOn f (Set.Icc ((X.lo : ℝ) / SCALE) ((X.hi : ℝ) / SCALE)))
    (hderiv : ∀ u ∈ Set.Ioo ((X.lo : ℝ) / SCALE) ((X.hi : ℝ) / SCALE), HasDerivAt f (f' u) u)
    (hok : centered1DPos fI fpI X = true)
    {x : ℝ} (hx : mem X x) : 0 < f x := by
  have hS := SCALE_pos
  unfold centered1DPos at hok; dsimp only at hok
  split_ifs at hok with hdir
  · exact pos_of_lo_pos (hfI X le_rfl le_rfl x hx) hdir
  · rw [decide_eq_true_eq] at hok
    set m : ℤ := (X.lo + X.hi) / 2
    set hw : ℤ := max (m - X.lo) (X.hi - m)
    set M : ℤ := absHi (fpI X)
    have hmlo : X.lo ≤ m := by omega
    have hmhi : m ≤ X.hi := by omega
    have hm_mem : ((m : ℝ) / SCALE) ∈ Set.Icc ((X.lo : ℝ) / SCALE) ((X.hi : ℝ) / SCALE) :=
      ⟨div_le_div_of_nonneg_right (by exact_mod_cast hmlo) (le_of_lt hS),
       div_le_div_of_nonneg_right (by exact_mod_cast hmhi) (le_of_lt hS)⟩
    have hM0 : (0 : ℝ) ≤ (M : ℝ) / SCALE := by
      have : 0 ≤ M := le_trans (abs_nonneg _) (le_max_left _ _)
      exact div_nonneg (by exact_mod_cast this) (le_of_lt hS)
    have hM_ub : ∀ u ∈ Set.Ioo ((X.lo : ℝ) / SCALE) ((X.hi : ℝ) / SCALE), |f' u| ≤ (M : ℝ) / SCALE := by
      intro u hu
      exact abs_le_absHi (hfpI u ⟨le_of_lt hu.1, le_of_lt hu.2⟩)
    have hmvt := mvt_centered_1d hM0 hcont hderiv hM_ub hm_mem ⟨hx.1, hx.2⟩
    have hhw_eq : max ((m : ℝ) / SCALE - (X.lo : ℝ) / SCALE) ((X.hi : ℝ) / SCALE - (m : ℝ) / SCALE)
        = (hw : ℝ) / SCALE := by
      simp only [hw, Int.cast_max, Int.cast_sub]
      rw [max_div_pos (le_of_lt hS), sub_div, sub_div]
    rw [hhw_eq] at hmvt
    have hfm : mem (fI (pt m)) (f ((m : ℝ) / SCALE)) := hfI (pt m) hmlo hmhi _ (mem_pt m)
    have hlb := mem_sub hfm (mem_mul (mem_pt M) (mem_pt hw))
    have hpos := pos_of_lo_pos hlb hok
    linarith

/-! ### Elementary Endpoint Bounds on `h(x)` and `phi(x)` -/

lemma neg_mul_log_le_h {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : -x * Real.log x ≤ h x := by
  unfold h
  rcases hx1.eq_or_lt with rfl | hlt
  · simp
  · have : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    nlinarith

lemma h_le_mul_one_sub_log {x : ℝ} (hx1 : x < 1) : h x ≤ x * (1 - Real.log x) := by
  unfold h
  have h1mx : 0 < 1 - x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos one_pos h1mx)
  rw [Real.log_div one_ne_zero (ne_of_gt h1mx), Real.log_one, zero_sub] at hlog
  have hmul : -(1 - x) * Real.log (1 - x) ≤ x := by
    have := mul_le_mul_of_nonneg_left hlog (le_of_lt h1mx)
    have hEq : (1 - x) * (1 / (1 - x) - 1) = x := by field_simp [ne_of_gt h1mx]; ring
    linarith
  linarith

/-- Concavity reduction: `h(x y) ≥ (809/1000)(y h(x) + x h(y))` follows from the 1D diagonal
    inequality `∀ s ∈ [0, 1], (809/500) s h(s) ≤ h(s^2)`. -/
lemma bopp2D_of_bopp1D (h1d : ∀ s, 0 ≤ s → s ≤ 1 → (809 / 500 : ℝ) * s * h s ≤ h (s ^ 2)) :
    ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → (809 / 1000 : ℝ) * (y * h x + x * h y) ≤ h (x * y) := by
  intro x y hx0 hx1 hy0 hy1
  rcases hx0.eq_or_lt with rfl | hx_pos
  · simp [h_zero]
  rcases hy0.eq_or_lt with rfl | hy_pos
  · simp [h_zero]
  rcases hx1.eq_or_lt with rfl | hx_lt
  · simp [h_one]; have := h_nonneg (le_of_lt hy_pos) hy1; linarith
  rcases hy1.eq_or_lt with rfl | hy_lt
  · simp [h_one]; have := h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt); linarith
  set G : ℝ → ℝ := fun u => Real.exp u * h (Real.exp (-u))
  set G' : ℝ → ℝ := fun u => -(Real.exp u * Real.log (1 - Real.exp (-u)))
  have hG_deriv : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt G (G' u) u := by
    intro u hu
    have heu : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Set.mem_Ioi.mp hu])
    have heu0 : 0 < Real.exp (-u) := Real.exp_pos (-u)
    have h1m : 0 < 1 - Real.exp (-u) := by linarith
    have hd_e : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-u)) u := by
      have := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_id' u).neg
      exact this.congr_deriv (by ring)
    have hd_h : HasDerivAt (fun t : ℝ => h (Real.exp (-t))) (hp (Real.exp (-u)) * (-Real.exp (-u))) u := by
      simpa [Function.comp_def] using (hasDerivAt_h heu0 heu).comp u hd_e
    have hd_mul := (Real.hasDerivAt_exp u).fun_mul hd_h
    exact hd_mul.congr_deriv (by
      unfold h hp G'
      rw [Real.log_exp (-u), Real.log_div (ne_of_gt h1m) (ne_of_gt heu0), Real.log_exp (-u)]
      have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
      calc Real.exp u * (-Real.exp (-u) * -u - (1 - Real.exp (-u)) * Real.log (1 - Real.exp (-u)))
            + Real.exp u * ((Real.log (1 - Real.exp (-u)) - -u) * -Real.exp (-u))
          = u * (Real.exp u * Real.exp (-u)) - Real.exp u * Real.log (1 - Real.exp (-u))
            + (Real.exp u * Real.exp (-u)) * Real.log (1 - Real.exp (-u))
            - (Real.exp u * Real.exp (-u)) * Real.log (1 - Real.exp (-u))
            - u * (Real.exp u * Real.exp (-u)) := by ring
        _ = -(Real.exp u * Real.log (1 - Real.exp (-u))) := by rw [hprod]; ring)
  have hG'_deriv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt G' (-(Real.exp u * Real.log (1 - Real.exp (-u)) + 1 / (1 - Real.exp (-u)))) u := by
    intro u hu
    have heu : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Set.mem_Ioi.mp hu])
    have h1m : 0 < 1 - Real.exp (-u) := by linarith
    have hd_1m : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t)) (Real.exp (-u)) u := by
      have hd_e : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-u)) u := by
        have := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_id' u).neg
        exact this.congr_deriv (by ring)
      exact ((hasDerivAt_const u (1 : ℝ)).fun_sub hd_e).congr_deriv (by ring)
    have hd_log : HasDerivAt (fun t : ℝ => Real.log (1 - Real.exp (-t))) (Real.exp (-u) / (1 - Real.exp (-u))) u :=
      hd_1m.log (ne_of_gt h1m)
    have hd_prod := ((Real.hasDerivAt_exp u).fun_mul hd_log).fun_neg
    exact hd_prod.congr_deriv (by
      have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
      field_simp [ne_of_gt h1m]
      nlinarith [hprod])
  have hconc : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) G := by
    apply concaveOn_of_deriv2_nonpos (convex_Ioi 0)
    · intro u hu; exact (hG_deriv u hu).continuousAt.continuousWithinAt
    · intro u hu; rw [interior_Ioi] at hu
      exact (hG_deriv u hu).differentiableAt.differentiableWithinAt
    · intro u hu; rw [interior_Ioi] at hu
      have hdeq : deriv G =ᶠ[nhds u] G' := by
        filter_upwards [Ioi_mem_nhds hu] with v hv; exact (hG_deriv v hv).deriv
      exact ((hG'_deriv u hu).congr_of_eventuallyEq hdeq).differentiableAt.differentiableWithinAt
    · intro u hu; rw [interior_Ioi] at hu
      have hdeq : deriv G =ᶠ[nhds u] G' := by
        filter_upwards [Ioi_mem_nhds hu] with v hv; exact (hG_deriv v hv).deriv
      have h2 := ((hG'_deriv u hu).congr_of_eventuallyEq hdeq).deriv
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      rw [h2]
      set t := Real.exp (-u)
      have ht0 : 0 < t := Real.exp_pos (-u)
      have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith [Set.mem_Ioi.mp hu])
      have h1mt : 0 < 1 - t := by linarith
      have hlog := Real.log_le_sub_one_of_pos (div_pos one_pos h1mt)
      rw [Real.log_div one_ne_zero (ne_of_gt h1mt), Real.log_one, zero_sub] at hlog
      have hsum_nn : 0 ≤ Real.log (1 - t) + t / (1 - t) := by
        have hEq : 1 / (1 - t) - 1 = t / (1 - t) := by field_simp [ne_of_gt h1mt]; ring
        linarith
      have hprod : Real.exp u * t = 1 := by simp only [t]; rw [← Real.exp_add]; simp
      have hrew : Real.exp u * Real.log (1 - t) + 1 / (1 - t)
          = Real.exp u * (Real.log (1 - t) + t / (1 - t)) := by
        field_simp [ne_of_gt h1mt]; nlinarith [hprod]
      have hnn : 0 ≤ Real.exp u * (Real.log (1 - t) + t / (1 - t)) :=
        mul_nonneg (le_of_lt (Real.exp_pos u)) hsum_nn
      linarith
  set ux := -Real.log x
  set uy := -Real.log y
  have hux : ux ∈ Set.Ioi (0 : ℝ) := by simp [ux, Real.log_neg hx_pos hx_lt]
  have huy : uy ∈ Set.Ioi (0 : ℝ) := by simp [uy, Real.log_neg hy_pos hy_lt]
  have hmid := hconc.2 hux huy (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  set s := Real.sqrt (x * y)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (mul_pos hx_pos hy_pos)
  have hs1 : s ≤ 1 := by
    have : x * y ≤ 1 := by nlinarith
    calc Real.sqrt (x * y) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt this
      _ = 1 := Real.sqrt_one
  have hs2 : s ^ 2 = x * y := Real.sq_sqrt (mul_nonneg (le_of_lt hx_pos) (le_of_lt hy_pos))
  have hGx : G ux = h x / x := by
    simp only [G, ux, Real.exp_neg, Real.exp_log hx_pos, inv_inv, div_eq_inv_mul]
  have hGy : G uy = h y / y := by
    simp only [G, uy, Real.exp_neg, Real.exp_log hy_pos, inv_inv, div_eq_inv_mul]
  have hGmid : G ((1 / 2 : ℝ) * ux + (1 / 2 : ℝ) * uy) = h s / s := by
    have harg : (1 / 2 : ℝ) * ux + (1 / 2 : ℝ) * uy = -Real.log s := by
      have hlog_s : Real.log s = (1 / 2 : ℝ) * (Real.log x + Real.log y) := by
        have := Real.log_sqrt (mul_nonneg (le_of_lt hx_pos) (le_of_lt hy_pos))
        rw [Real.log_mul (ne_of_gt hx_pos) (ne_of_gt hy_pos)] at this
        simp only [s]; linarith
      simp only [ux, uy]; linarith
    rw [harg]; simp only [G, Real.exp_neg, Real.exp_log hs0, inv_inv, div_eq_inv_mul]
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hGx, hGy, hGmid] at hmid
  have hxy_pos : 0 < x * y := mul_pos hx_pos hy_pos
  have hcomb : y * h x + x * h y ≤ 2 * s * h s := by
    have hmul := mul_le_mul_of_nonneg_left hmid (le_of_lt hxy_pos)
    have hL : x * y * ((1 / 2 : ℝ) * (h x / x) + (1 / 2 : ℝ) * (h y / y)) = (1 / 2 : ℝ) * (y * h x + x * h y) := by
      field_simp [ne_of_gt hx_pos, ne_of_gt hy_pos]
    have hR : x * y * (h s / s) = s * h s := by
      rw [← hs2]; field_simp [ne_of_gt hs0]
    linarith
  have hdiag := h1d s (le_of_lt hs0) hs1
  rw [hs2] at hdiag
  linarith

end UCBound.Cert
