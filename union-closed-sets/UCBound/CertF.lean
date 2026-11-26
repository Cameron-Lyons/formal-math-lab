module

public import UCBound.Cert2DMem
public import UCBound.CertStrips
public import UCBound.CertFRChk1
public import UCBound.CertFRChk2
public import UCBound.CertFvChk1
public import UCBound.CertFvChk2
public import UCBound.CertFsimChk1
public import UCBound.CertFsimChk2

@[expose] public section

/-!
# Unified Certified 2D `F`-Inequalities (`hF_R`, `hF_v`, `hF_sim`)

Proves all three symmetric lower bounds on `F_fun x y`:
- `cert_F_R`:   `(11/200) * (phi x * R y + phi y * R x) ≤ F(x, y)`
- `cert_F_v`:   `(21/100) * (v x ^ 2 * phi y + v y ^ 2 * phi x) ≤ F(x, y)`
- `cert_F_sim`: `(3/100) * (phi x * R y + phi y * R x) + (13/100) * (v x ^ 2 * phi y + v y ^ 2 * phi x) ≤ F(x, y)`

via a single generic theorem `cert_F_combo` covering the boundary strips (`CertStrips`),
the Hessian-positive-definite contact square near `(rStar, rStar)`, and the 7 compact
centered-form 2D boxes.
-/

namespace UCBound.Cert2D

open UCBound UCBound.Iv UCBound.Cert UCBound.FastIv

/-! ### Generic Parameterized Family `G_F a b` and Its Derivatives -/

private noncomputable def wv_fun (x : ℝ) : ℝ := v_fun x ^ 2
private noncomputable def wvP (x : ℝ) : ℝ := 2 * (v_fun x * vP x)
private noncomputable def wvPP (x : ℝ) : ℝ := 2 * (vP x ^ 2 + v_fun x * vPP x)

private noncomputable def G_F (a b x y : ℝ) : ℝ :=
  F_fun x y - a * (phi x * R_fun y + phi y * R_fun x) - b * (wv_fun x * phi y + wv_fun y * phi x)

private noncomputable def Gx_F (a b x y : ℝ) : ℝ :=
  Fx_fun x y - a * (phiP x * R_fun y + phi y * RP x) - b * (wvP x * phi y + wv_fun y * phiP x)

private noncomputable def Hxx_F (a b x y : ℝ) : ℝ :=
  Fxx_fun x y - a * (phiPP x * R_fun y + phi y * RPP x) - b * (wvPP x * phi y + wv_fun y * phiPP x)

private noncomputable def Hxy_F (a b x y : ℝ) : ℝ :=
  Fxy_fun x y - a * (phiP x * RP y + phiP y * RP x) - b * (wvP x * phiP y + wvP y * phiP x)

private lemma hasDerivAt_wv {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt wv_fun (wvP x) x := by
  have h1 := hasDerivAt_v hx0 hx1
  have hfun : wv_fun = fun t => v_fun t * v_fun t := by ext t; unfold wv_fun; ring
  rw [hfun]; exact (h1.fun_mul h1).congr_deriv (by unfold wvP; ring)

private lemma hasDerivAt_wvP {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : HasDerivAt wvP (wvPP x) x :=
  (((hasDerivAt_v hx0 hx1).fun_mul (hasDerivAt_vP hx0 hx1)).const_mul 2).congr_deriv (by unfold wvPP; ring)

private lemma hasDerivAt_G_F_x {a b x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun t => G_F a b t y) (Gx_F a b x y) x := by
  have hd1 := hasDerivAt_F_x hx0 hx1 hy0 hy1
  have hd2 := (((hasDerivAt_phi hx0 hx1).mul_const (R_fun y)).fun_add ((hasDerivAt_R hx0 hx1).const_mul (phi y))).const_mul a
  have hd3 := (((hasDerivAt_wv hx0 hx1).mul_const (phi y)).fun_add ((hasDerivAt_phi hx0 hx1).const_mul (wv_fun y))).const_mul b
  exact ((hd1.fun_sub hd2).fun_sub hd3).congr_deriv (by unfold Gx_F; ring)

/-! ### Generic Leaf Soundness (`okF_sound` and `okFHess_sound`) -/

private lemma okF_sound {a b : ℝ} {G_iv Gx_iv : Interval → Interval → Interval}
    (hG : ∀ {X Y I J : Interval} {u v : ℝ}, fGuard2DF X Y = true →
      X.lo ≤ I.lo → I.hi ≤ X.hi → Y.lo ≤ J.lo → J.hi ≤ Y.hi →
      mem I u → mem J v → mem (G_iv I J) (G_F a b u v))
    (hGx : ∀ {X Y : Interval} {u v : ℝ}, fGuard2DF X Y = true →
      mem X u → mem Y v → mem (Gx_iv X Y) (Gx_F a b u v))
    (hGx_pt : ∀ {X Y : Interval} {mx : ℤ} {v : ℝ}, fGuard2DF X Y = true →
      X.lo ≤ mx → mx ≤ X.hi →
      mem Y v → mem (Gx_iv Y (pt mx)) (Gx_F a b v ((mx : ℝ) / SCALE)))
    {w : LeafW} {X Y : Interval}
    (hok : (match w with | .skip => decide (Y.hi < X.lo) | .hess => false | _ => fGuard2DF X Y && centered2DWPos G_iv Gx_iv (fun U V => Gx_iv V U) w X Y) = true)
    {x y : ℝ} (hx : mem X x) (hy : mem Y y) (hxy : x ≤ y) :
    0 ≤ G_F a b x y := by
  have hS := SCALE_pos
  cases w with
  | hess => simp at hok
  | skip =>
    simp only [decide_eq_true_eq] at hok
    have : (Y.hi : ℝ) / SCALE < (X.lo : ℝ) / SCALE := div_lt_div_of_pos_right (by exact_mod_cast hok) hS
    linarith [hx.1, hy.2]
  | direct | centered =>
    simp only [Bool.and_eq_true] at hok
    have hg := hok.1
    have hg' := hg; unfold fGuard2DF at hg'
    simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, Bool.and_eq_true, decide_eq_true_eq] at hg'
    have hgX := hg'.1.1; have hgY := hg'.1.2
    have hgX' := hgX; unfold fGuardD1 at hgX'
    simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgX'
    have hgY' := hgY; unfold fGuardD1 at hgY'
    simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgY'
    have hXle : X.lo ≤ X.hi := hgX'.1.1.1.1.1.1.2
    have hYle : Y.lo ≤ Y.hi := hgY'.1.1.1.1.1.1.2
    exact le_of_lt (centered2DWPos_sound (G := G_F a b) (Gx := Gx_F a b) (Gy := fun u v => Gx_F a b v u)
      hXle hYle
      (fun I J hIlo hIhi hJlo hJhi u v hu hv => hG hg hIlo hIhi hJlo hJhi hu hv)
      (fun u v hu hv => hGx hg hu hv)
      (fun v hv => hGx_pt hg (by omega) (by omega) hv)
      (fun v hv u hu => (hasDerivAt_G_F_x (fGuardD1_bounds hgX hu).1 (fGuardD1_bounds hgX hu).2
        (fGuardD1_bounds hgY hv).1 (fGuardD1_bounds hgY hv).2).continuousAt.continuousWithinAt)
      (fun v hv u hu => hasDerivAt_G_F_x (fGuardD1_bounds hgX (Set.Ioo_subset_Icc_self hu)).1
        (fGuardD1_bounds hgX (Set.Ioo_subset_Icc_self hu)).2 (fGuardD1_bounds hgY hv).1 (fGuardD1_bounds hgY hv).2)
      (fun v hv => by
        set mx := (X.lo + X.hi) / 2
        have hmxX : mem X ((mx : ℝ) / SCALE) := mem_sub_pt_le (by omega) (by omega) _ (mem_pt mx)
        have hsym : (fun s => G_F a b ((mx : ℝ) / SCALE) s) = fun s => G_F a b s ((mx : ℝ) / SCALE) := by
          ext s; unfold G_F; rw [F_fun_symm]; ring
        rw [hsym]
        exact (hasDerivAt_G_F_x (fGuardD1_bounds hgY hv).1 (fGuardD1_bounds hgY hv).2
          (fGuardD1_bounds hgX hmxX).1 (fGuardD1_bounds hgX hmxX).2).continuousAt.continuousWithinAt)
      (fun v hv => by
        set mx := (X.lo + X.hi) / 2
        have hmxX : mem X ((mx : ℝ) / SCALE) := mem_sub_pt_le (by omega) (by omega) _ (mem_pt mx)
        have hsym : (fun s => G_F a b ((mx : ℝ) / SCALE) s) = fun s => G_F a b s ((mx : ℝ) / SCALE) := by
          ext s; unfold G_F; rw [F_fun_symm]; ring
        rw [hsym]
        exact hasDerivAt_G_F_x (fGuardD1_bounds hgY (Set.Ioo_subset_Icc_self hv)).1
          (fGuardD1_bounds hgY (Set.Ioo_subset_Icc_self hv)).2 (fGuardD1_bounds hgX hmxX).1 (fGuardD1_bounds hgX hmxX).2)
      hok.2 hx hy)

private lemma okFHess_sound {a b : ℝ} {Hxx_iv Hxy_iv : Interval → Interval → Interval}
    (hHxx : ∀ {X Y : Interval} {u v : ℝ}, fGuard2DFHess X Y = true →
      mem X u → mem Y v → mem (Hxx_iv X Y) (Hxx_F a b u v))
    (hHxy : ∀ {X Y : Interval} {u v : ℝ}, fGuard2DFHess X Y = true →
      mem X u → mem Y v → mem (Hxy_iv X Y) (Hxy_F a b u v))
    {w : LeafW} {X Y : Interval}
    (hok : (match w with | .skip => decide (Y.hi < X.lo) | .hess => fGuard2DFHess X Y && hess2DPD (Hxx_iv X Y) (Hxx_iv Y X) (Hxy_iv X Y) | _ => false) = true)
    {u v : ℝ} (hu : mem X u) (hv : mem Y v) (huv : u ≤ v) (dx dy : ℝ) :
    0 ≤ Hxx_F a b u v * dx ^ 2 + 2 * Hxy_F a b u v * dx * dy + Hxx_F a b v u * dy ^ 2 := by
  have hS := SCALE_pos
  cases w with
  | direct | centered => simp at hok
  | skip =>
    simp only [decide_eq_true_eq] at hok
    have : (Y.hi : ℝ) / SCALE < (X.lo : ℝ) / SCALE := div_lt_div_of_pos_right (by exact_mod_cast hok) hS
    linarith [hu.1, hv.2]
  | hess =>
    simp only [Bool.and_eq_true] at hok
    have hg := hok.1
    have hg_sym : fGuard2DFHess Y X = true := by
      have hg' := hg; unfold fGuard2DFHess at hg'
      simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, Bool.and_eq_true, decide_eq_true_eq] at hg'
      unfold fGuard2DFHess; simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hg'.1.2, hg'.1.1⟩, ?_⟩
      rw [mul_comm_iv Y X]; exact hg'.2
    exact hess2DPD_quad_nonneg hok.2 (hHxx hg hu hv) (hHxx hg_sym hv hu) (hHxy hg hu hv)

/-! ### Generic Assembly Theorem (`cert_F_combo`) -/

private lemma cert_F_combo {a b : ℝ} {ok okH : LeafW → Interval → Interval → Bool}
    {p01 p68 p70 p999 p99999 : ℤ} {t0 t1 t2 t3 t4 t5 t6 t7 : Tree2DW}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hstrip : a + (9 / 50 : ℝ) * b ≤ 11 / 200)
    (hp01 : (p01 : ℝ) / SCALE ≤ 1 / 100)
    (hp99999 : (99999 / 100000 : ℝ) ≤ (p99999 : ℝ) / SCALE)
    (hr_lo : p68 ≤ constIv.r.lo) (hr_hi : constIv.r.hi ≤ p70)
    (hp68_pos : 0 < p68) (hp70_lt : p70 < (SCALE : ℤ))
    (hok : ∀ w X Y, ok w X Y = true → ∀ u v, mem X u → mem Y v → u ≤ v → 0 ≤ G_F a b u v)
    (hokH : ∀ w X Y, okH w X Y = true → ∀ u v, mem X u → mem Y v → u ≤ v →
      ∀ dx dy, 0 ≤ Hxx_F a b u v * dx ^ 2 + 2 * Hxy_F a b u v * dx * dy + Hxx_F a b v u * dy ^ 2)
    (hb0_chk : check2DW ok p01 p68 p01 p68 t0 = true)
    (hb1_chk : check2DW ok p01 p68 p68 p70 t1 = true)
    (hb2_chk : check2DW ok p01 p68 p70 p999 t2 = true)
    (hb3_chk : check2DW okH p68 p70 p68 p70 t3 = true)
    (hb4_chk : check2DW ok p68 p70 p70 p999 t4 = true)
    (hb5_chk : check2DW ok p70 p999 p70 p999 t5 = true)
    (hb6_chk : check2DW ok p01 p999 p999 p99999 t6 = true)
    (hb7_chk : check2DW ok p999 p99999 p999 p99999 t7 = true) :
    ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      a * (phi x * R_fun y + phi y * R_fun x) + b * (v_fun x ^ 2 * phi y + v_fun y ^ 2 * phi x) ≤ F_fun x y := by
  suffices hsym : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → x ≤ y → 0 ≤ G_F a b x y by
    intro x y hx0 hx1 hy0 hy1
    rcases le_total x y with hle | hle
    · have := hsym x y hx0 hx1 hy0 hy1 hle; unfold G_F wv_fun at this; linarith
    · have := hsym y x hy0 hy1 hx0 hx1 hle; unfold G_F wv_fun at this; rw [F_fun_symm] at this; linarith
  have hS := SCALE_pos
  have hcontact : ∀ x y, mem ⟨p68, p70⟩ x → mem ⟨p68, p70⟩ y → 0 ≤ G_F a b x y := by
    intro x y hx hy
    have hr_lo' : (p68 : ℝ) / SCALE ≤ rStar :=
      le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hr_lo) (le_of_lt hS)) validConstIv.hr_mem.1
    have hr_hi' : rStar ≤ (p70 : ℝ) / SCALE :=
      le_trans validConstIv.hr_mem.2 (div_le_div_of_nonneg_right (by exact_mod_cast hr_hi) (le_of_lt hS))
    have hlo0 : (0 : ℝ) < (p68 : ℝ) / SCALE := div_pos (by exact_mod_cast hp68_pos) hS
    have hhi1 : (p70 : ℝ) / SCALE < 1 := (div_lt_one hS).mpr (by exact_mod_cast hp70_lt)
    have hv0 : v_fun rStar = 0 := by unfold v_fun hr; rw [phi_rStar]; ring
    have hG0 : G_F a b rStar rStar = 0 := by
      unfold G_F wv_fun; rw [contact_F.1, contact_derivs.2.1, hv0]; ring
    have hGx0 : Gx_F a b rStar rStar = 0 := by
      unfold Gx_F wv_fun wvP; rw [contact_F.2, contact_derivs.2.1, contact_derivs.2.2.1, hv0]; ring
    have hHxy_symm : ∀ u v, Hxy_F a b v u = Hxy_F a b u v := fun u v => by
      unfold Hxy_F Fxy_fun; rw [mul_comm v u]; ring
    exact nonneg_of_hess_pd_square' (G := G_F a b) (Gx := Gx_F a b) (Hxx := Hxx_F a b) (Hxy := Hxy_F a b)
      hr_lo' hr_hi' hG0 hGx0
      (fun x' y' s hu1 hu2 hv1 hv2 => by
        have hu0 : 0 < rStar + s * (x' - rStar) := lt_of_lt_of_le hlo0 hu1
        have hu1' : rStar + s * (x' - rStar) < 1 := lt_of_le_of_lt hu2 hhi1
        have hv0' : 0 < rStar + s * (y' - rStar) := lt_of_lt_of_le hlo0 hv1
        have hv1' : rStar + s * (y' - rStar) < 1 := lt_of_le_of_lt hv2 hhi1
        have hdF := hasDerivAt_F_line hu0 hu1' hv0' hv1'
        have hdR := (hasDerivAt_symProd_line (hasDerivAt_phi hu0 hu1') (hasDerivAt_phi hv0' hv1')
          (hasDerivAt_R hu0 hu1') (hasDerivAt_R hv0' hv1')).const_mul a
        have hdV := (hasDerivAt_symProd_line (hasDerivAt_wv hu0 hu1') (hasDerivAt_wv hv0' hv1')
          (hasDerivAt_phi hu0 hu1') (hasDerivAt_phi hv0' hv1')).const_mul b
        exact ((hdF.fun_sub hdR).fun_sub hdV).congr_deriv (by unfold Gx_F; ring))
      (fun x' y' s hu1 hu2 hv1 hv2 => by
        have hu0 : 0 < rStar + s * (x' - rStar) := lt_of_lt_of_le hlo0 hu1
        have hu1' : rStar + s * (x' - rStar) < 1 := lt_of_le_of_lt hu2 hhi1
        have hv0' : 0 < rStar + s * (y' - rStar) := lt_of_lt_of_le hlo0 hv1
        have hv1' : rStar + s * (y' - rStar) < 1 := lt_of_le_of_lt hv2 hhi1
        have hdFx1 := (hasDerivAt_Fx_line hu0 hu1' hv0' hv1').mul_const (x' - rStar)
        have hdFx2 := (hasDerivAt_Fx_line hv0' hv1' hu0 hu1').mul_const (y' - rStar)
        have hdR := (hasDerivAt_symProd_dline (hasDerivAt_phi hu0 hu1') (hasDerivAt_phi hv0' hv1')
          (hasDerivAt_phiP hu0 hu1') (hasDerivAt_phiP hv0' hv1')
          (hasDerivAt_R hu0 hu1') (hasDerivAt_R hv0' hv1')
          (hasDerivAt_RP hu0 hu1') (hasDerivAt_RP hv0' hv1')).const_mul a
        have hdV := (hasDerivAt_symProd_dline (hasDerivAt_wv hu0 hu1') (hasDerivAt_wv hv0' hv1')
          (hasDerivAt_wvP hu0 hu1') (hasDerivAt_wvP hv0' hv1')
          (hasDerivAt_phi hu0 hu1') (hasDerivAt_phi hv0' hv1')
          (hasDerivAt_phiP hu0 hu1') (hasDerivAt_phiP hv0' hv1')).const_mul b
        have hfun : (fun t => Gx_F a b (rStar + t * (x' - rStar)) (rStar + t * (y' - rStar)) * (x' - rStar) +
                              Gx_F a b (rStar + t * (y' - rStar)) (rStar + t * (x' - rStar)) * (y' - rStar))
            = fun t => (Fx_fun (rStar + t * (x' - rStar)) (rStar + t * (y' - rStar)) * (x' - rStar) +
                        Fx_fun (rStar + t * (y' - rStar)) (rStar + t * (x' - rStar)) * (y' - rStar))
              - a * ((phiP (rStar + t * (x' - rStar)) * R_fun (rStar + t * (y' - rStar)) +
                      phi (rStar + t * (y' - rStar)) * RP (rStar + t * (x' - rStar))) * (x' - rStar) +
                     (phiP (rStar + t * (y' - rStar)) * R_fun (rStar + t * (x' - rStar)) +
                      phi (rStar + t * (x' - rStar)) * RP (rStar + t * (y' - rStar))) * (y' - rStar))
              - b * ((wvP (rStar + t * (x' - rStar)) * phi (rStar + t * (y' - rStar)) +
                      wv_fun (rStar + t * (y' - rStar)) * phiP (rStar + t * (x' - rStar))) * (x' - rStar) +
                     (wvP (rStar + t * (y' - rStar)) * phi (rStar + t * (x' - rStar)) +
                      wv_fun (rStar + t * (x' - rStar)) * phiP (rStar + t * (y' - rStar))) * (y' - rStar)) := by
          ext t; unfold Gx_F; ring
        rw [hfun]
        exact (((hdFx1.fun_add hdFx2).fun_sub hdR).fun_sub hdV).congr_deriv (by
          unfold Hxx_F Hxy_F Fxy_fun
          rw [mul_comm (rStar + s * (y' - rStar)) (rStar + s * (x' - rStar))]; ring))
      hHxy_symm
      (fun u v hu1 hu2 hv1 hv2 huv dx dy =>
        check2DW_sym_sound (fun w X Y h a' b' ha' hb' hab => hokH w X Y h a' b' ha' hb' hab dx dy)
          hb3_chk ⟨hu1, hu2⟩ ⟨hv1, hv2⟩ huv)
      hx.1 hx.2 hy.1 hy.2
  intro x y hx0 hx1 hy0 hy1 hxy
  by_cases hx01 : x ≤ 1 / 100
  · have hst := cert_F_strip_low x y hx0 hx01 hy0 hy1
    have hRx := cert_R_le_phi x hx0 hx1
    have hRy := cert_R_nonneg y hy0 hy1
    have hvx := cert_v_sq_le_phi x hx0 hx1
    have hvy := cert_v_sq_le_phi y hy0 hy1
    have hpx := phi_nonneg x; have hpy := phi_nonneg y
    have h1 : a * (phi x * R_fun y + phi y * R_fun x) ≤ (11 / 200 : ℝ) * phi x * R_fun y + a * (phi x * phi y) := by
      have ha11 : a ≤ 11 / 200 := by linarith
      nlinarith [mul_nonneg hpx hRy, mul_le_mul_of_nonneg_left hRx hpy]
    have h2 : b * (v_fun x ^ 2 * phi y + v_fun y ^ 2 * phi x) ≤ (9 / 50 : ℝ) * b * (phi x * phi y) := by
      nlinarith [mul_le_mul_of_nonneg_right hvx hpy, mul_le_mul_of_nonneg_right hvy hpx]
    unfold G_F wv_fun F_fun; unfold B_fun AR_fun at hst
    nlinarith [mul_nonneg hpx hpy]
  · push Not at hx01
    by_cases hyhi : 99999 / 100000 ≤ y
    · have hst := cert_F_strip_high y x hyhi hy1 hx0 hx1
      have hRy := cert_R_le_phi y hy0 hy1
      have hRx := cert_R_nonneg x hx0 hx1
      have hvx := cert_v_sq_le_phi x hx0 hx1
      have hvy := cert_v_sq_le_phi y hy0 hy1
      have hpx := phi_nonneg x; have hpy := phi_nonneg y
      have h1 : a * (phi x * R_fun y + phi y * R_fun x) ≤ (11 / 200 : ℝ) * phi y * R_fun x + a * (phi x * phi y) := by
        have ha11 : a ≤ 11 / 200 := by linarith
        nlinarith [mul_nonneg hpy hRx, mul_le_mul_of_nonneg_left hRy hpx]
      have h2 : b * (v_fun x ^ 2 * phi y + v_fun y ^ 2 * phi x) ≤ (9 / 50 : ℝ) * b * (phi x * phi y) := by
        nlinarith [mul_le_mul_of_nonneg_right hvx hpy, mul_le_mul_of_nonneg_right hvy hpx]
      unfold G_F wv_fun F_fun; unfold B_fun AR_fun at hst
      rw [mul_comm y x] at hst
      nlinarith [mul_nonneg hpx hpy]
    · push Not at hyhi
      have hx_lo : (p01 : ℝ) / SCALE ≤ x := by linarith
      have hy_hi : y ≤ (p99999 : ℝ) / SCALE := by linarith
      by_cases hy999 : y ≤ (p999 : ℝ) / SCALE
      · by_cases hx68 : x ≤ (p68 : ℝ) / SCALE
        · by_cases hy68 : y ≤ (p68 : ℝ) / SCALE
          · exact check2DW_sym_sound hok hb0_chk ⟨hx_lo, hx68⟩ ⟨le_trans hx_lo hxy, hy68⟩ hxy
          · push Not at hy68
            by_cases hy70 : y ≤ (p70 : ℝ) / SCALE
            · exact check2DW_sym_sound hok hb1_chk ⟨hx_lo, hx68⟩ ⟨le_of_lt hy68, hy70⟩ hxy
            · push Not at hy70
              exact check2DW_sym_sound hok hb2_chk ⟨hx_lo, hx68⟩ ⟨le_of_lt hy70, hy999⟩ hxy
        · push Not at hx68
          by_cases hx70 : x ≤ (p70 : ℝ) / SCALE
          · by_cases hy70 : y ≤ (p70 : ℝ) / SCALE
            · exact hcontact x y ⟨le_of_lt hx68, hx70⟩ ⟨le_trans (le_of_lt hx68) hxy, hy70⟩
            · push Not at hy70
              exact check2DW_sym_sound hok hb4_chk ⟨le_of_lt hx68, hx70⟩ ⟨le_of_lt hy70, hy999⟩ hxy
          · push Not at hx70
            exact check2DW_sym_sound hok hb5_chk ⟨le_of_lt hx70, le_trans hxy hy999⟩ ⟨le_trans (le_of_lt hx70) hxy, hy999⟩ hxy
      · push Not at hy999
        by_cases hx999 : x ≤ (p999 : ℝ) / SCALE
        · exact check2DW_sym_sound hok hb6_chk ⟨hx_lo, hx999⟩ ⟨le_of_lt hy999, hy_hi⟩ hxy
        · push Not at hx999
          exact check2DW_sym_sound hok hb7_chk ⟨le_of_lt hx999, le_trans hxy hy_hi⟩ ⟨le_of_lt hy999, hy_hi⟩ hxy

/-! ### Shared Interval Containment Helpers for `R`- and `v^2`-Terms -/

private lemma guard2DF_extract {X Y : Interval} (hg : fGuard2DF X Y = true) :
    fGuardD1 X = true ∧ fGuardD1 Y = true := by
  unfold fGuard2DF at hg
  simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  exact hg.1

private lemma guard2DFHess_extract {X Y : Interval} (hg : fGuard2DFHess X Y = true) :
    fGuardD2 X = true ∧ fGuardD2 Y = true ∧ fGuardD1 X = true ∧ fGuardD1 Y = true := by
  unfold fGuard2DFHess at hg
  simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  have hgX := hg.1.1; have hgY := hg.1.2
  have hgX' := hgX; unfold fGuardD2 at hgX'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgX'
  have hgY' := hgY; unfold fGuardD2 at hgY'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgY'
  exact ⟨hgX, hgY, hgX'.1.1.1, hgY'.1.1.1⟩

private lemma sub_box_bounds {X I : Interval} (hgX : fGuardD1 X = true)
    (hlo : X.lo ≤ I.lo) (hhi : I.hi ≤ X.hi) {u : ℝ} (hu : mem I u) : 0 < u ∧ u < 1 :=
  fGuardD1_bounds hgX
    ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt SCALE_pos)) hu.1,
     le_trans hu.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt SCALE_pos))⟩

private lemma mem_cFR_11 : mem cFR_11 (11 / 200 : ℝ) := by unfold cFR_11; simpa using mem_ofRat (p := 11) (q := 200) (by norm_num)
private lemma mem_cFv_21 : mem cFv_21 (21 / 100 : ℝ) := by unfold cFv_21; simpa using mem_ofRat (p := 21) (q := 100) (by norm_num)
private lemma mem_cFsim_3 : mem cFsim_3 (3 / 100 : ℝ) := by unfold cFsim_3; simpa using mem_ofRat (p := 3) (q := 100) (by norm_num)
private lemma mem_cFsim_13 : mem cFsim_13 (13 / 100 : ℝ) := by unfold cFsim_13; simpa using mem_ofRat (p := 13) (q := 100) (by norm_num)

/-! ### 1. `cert_F_R` -/

theorem cert_F_R : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    (11 / 200 : ℝ) * (phi x * R_fun y + phi y * R_fun x) ≤ F_fun x y := by
  have h := cert_F_combo (a := 11 / 200) (b := 0) (ok := okFR) (okH := okFRHess)
    (by norm_num) le_rfl (by norm_num)
    (by unfold p01_FR SCALE; norm_num) (by unfold p99999_FR SCALE; norm_num)
    (by decide) (by decide) (by decide) (by decide)
    (fun w X Y hok u v hu hv huv => okF_sound (a := 11 / 200) (b := 0) (G_iv := G_FR) (Gx_iv := Gx_FR)
      (fun hg hIlo hIhi hJlo hJhi hu' hv' => by
        have ⟨hgX, hgY⟩ := guard2DF_extract hg
        have hu01 := sub_box_bounds hgX hIlo hIhi hu'; have hv01 := sub_box_bounds hgY hJlo hJhi hv'
        unfold G_FR G_F; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fastF_of_eq, fastR_of_eq, zero_mul, sub_zero]
        exact mem_sub (mem_fastF validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2) hv' (le_of_lt hv01.1) (le_of_lt hv01.2))
          (mem_mul mem_cFR_11 (mem_add (mem_mul (mem_fastPhi validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2)) (mem_fastR validConstIv qL_lo_pos hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastR validConstIv qL_lo_pos hu' (le_of_lt hu01.1) (le_of_lt hu01.2))))))
      (fun hg hu' hv' => by
        have ⟨hgX, hgY⟩ := guard2DF_extract hg; have hv01 := fGuardD1_bounds hgY hv'
        unfold Gx_FR Gx_F; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fastFx_of_eq, fastR_of_eq, fastRP_of_eq, zero_mul, sub_zero]
        exact mem_sub (mem_fastFx hg hu' hv')
          (mem_mul mem_cFR_11 (mem_add (mem_mul (mem_fastPhiP_of_guard hgX hu') (mem_fastR validConstIv qL_lo_pos hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastRP_of_guard hgX hu')))))
      (fun hg hlo hhi hv' => by
        have ⟨hgX, hgY⟩ := guard2DF_extract hg
        have hmx01 := fGuardD1_bounds hgX (mem_sub_pt_le hlo hhi _ (mem_pt _))
        unfold Gx_FR Gx_F; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fastFx_of_eq, fastR_of_eq, fastRP_of_eq, zero_mul, sub_zero]
        exact mem_sub (mem_fastFx_pt hg hlo hhi hv')
          (mem_mul mem_cFR_11 (mem_add (mem_mul (mem_fastPhiP_of_guard hgY hv') (mem_fastR validConstIv qL_lo_pos (mem_pt _) (le_of_lt hmx01.1) (le_of_lt hmx01.2)))
            (mem_mul (mem_fastPhi validConstIv (mem_pt _) (le_of_lt hmx01.1) (le_of_lt hmx01.2)) (mem_fastRP_of_guard hgY hv')))))
      hok hu hv huv)
    (fun w X Y hok u v hu hv huv dx dy => okFHess_sound (a := 11 / 200) (b := 0) (Hxx_iv := Hxx_FR) (Hxy_iv := Hxy_FR)
      (fun hg hu' hv' => by
        have ⟨hgX, _, _, hgY1⟩ := guard2DFHess_extract hg; have hv01 := fGuardD1_bounds hgY1 hv'
        unfold Hxx_FR Hxx_F; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, zero_mul, sub_zero]
        exact mem_sub (mem_fastFxx hg hu' hv')
          (mem_mul mem_cFR_11 (mem_add (mem_mul (mem_fastPhiPP_of_guard hgX hu') (mem_fastR validConstIv qL_lo_pos hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastRPP_of_guard hgX hu')))))
      (fun hg hu' hv' => by
        have ⟨_, _, hgX1, hgY1⟩ := guard2DFHess_extract hg
        unfold Hxy_FR Hxy_F; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, zero_mul, sub_zero]
        exact mem_sub (mem_fastFxy hg hu' hv')
          (mem_mul mem_cFR_11 (mem_add (mem_mul (mem_fastPhiP_of_guard hgX1 hu') (mem_fastRP_of_guard hgY1 hv'))
            (mem_mul (mem_fastPhiP_of_guard hgY1 hv') (mem_fastRP_of_guard hgX1 hu')))))
      hok hu hv huv dx dy)
    chk_FR_b0 chk_FR_b1 chk_FR_b2 chk_FR_b3 chk_FR_b4 chk_FR_b5 chk_FR_b6 chk_FR_b7
  intro x y hx0 hx1 hy0 hy1; simpa using h x y hx0 hx1 hy0 hy1

/-! ### 2. `cert_F_v` -/

theorem cert_F_v : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    (21 / 100 : ℝ) * (v_fun x ^ 2 * phi y + v_fun y ^ 2 * phi x) ≤ F_fun x y := by
  have h := cert_F_combo (a := 0) (b := 21 / 100) (ok := okFv) (okH := okFvHess)
    le_rfl (by norm_num) (by norm_num)
    (by unfold p01_Fv SCALE; norm_num) (by unfold p99999_Fv SCALE; norm_num)
    (by decide) (by decide) (by decide) (by decide)
    (fun w X Y hok u v hu hv huv => okF_sound (a := 0) (b := 21 / 100) (G_iv := G_Fv) (Gx_iv := Gx_Fv)
      (fun hg hIlo hIhi hJlo hJhi hu' hv' => by
        have ⟨hgX, hgY⟩ := guard2DF_extract hg
        have hu01 := sub_box_bounds hgX hIlo hIhi hu'; have hv01 := sub_box_bounds hgY hJlo hJhi hv'
        unfold G_Fv G_F wv_fun; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fsq_eq, fastF_of_eq, fastV_of_eq, zero_mul, sub_zero]
        exact mem_sub (mem_fastF validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2) hv' (le_of_lt hv01.1) (le_of_lt hv01.2))
          (mem_mul mem_cFv_21 (mem_add (mem_mul (mem_sq (mem_fastV validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2))) (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_sq (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2))) (mem_fastPhi validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2))))))
      (fun hg hu' hv' => by
        have ⟨hgX, hgY⟩ := guard2DF_extract hg
        have hu01 := fGuardD1_bounds hgX hu'; have hv01 := fGuardD1_bounds hgY hv'
        have hres := mem_sub (mem_fastFx hg hu' hv')
          (mem_mul mem_cFv_21 (mem_add (mem_mul (mem_mul (mem_ofInt 2) (mem_mul (mem_fastV validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2)) (mem_fastVP_of_guard hgX hu')))
            (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_sq (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2))) (mem_fastPhiP_of_guard hgX hu'))))
        unfold Gx_Fv; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fsq_eq, fastFx_of_eq, fastV_of_eq, fastVP_of_eq]
        convert hres using 1; unfold Gx_F wvP wv_fun; push_cast; ring)
      (fun hg hlo hhi hv' => by
        have ⟨hgX, hgY⟩ := guard2DF_extract hg
        have hmx01 := fGuardD1_bounds hgX (mem_sub_pt_le hlo hhi _ (mem_pt _)); have hv01 := fGuardD1_bounds hgY hv'
        have hres := mem_sub (mem_fastFx_pt hg hlo hhi hv')
          (mem_mul mem_cFv_21 (mem_add (mem_mul (mem_mul (mem_ofInt 2) (mem_mul (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastVP_of_guard hgY hv')))
            (mem_fastPhi validConstIv (mem_pt _) (le_of_lt hmx01.1) (le_of_lt hmx01.2)))
            (mem_mul (mem_sq (mem_fastV validConstIv (mem_pt _) (le_of_lt hmx01.1) (le_of_lt hmx01.2))) (mem_fastPhiP_of_guard hgY hv'))))
        unfold Gx_Fv; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fsq_eq, fastFx_of_eq, fastV_of_eq, fastVP_of_eq]
        convert hres using 1; unfold Gx_F wvP wv_fun; push_cast; ring)
      hok hu hv huv)
    (fun w X Y hok u v hu hv huv dx dy => okFHess_sound (a := 0) (b := 21 / 100) (Hxx_iv := Hxx_Fv) (Hxy_iv := Hxy_Fv)
      (fun hg hu' hv' => by
        have ⟨hgX, _, hgX1, hgY1⟩ := guard2DFHess_extract hg
        have hu01 := fGuardD1_bounds hgX1 hu'; have hv01 := fGuardD1_bounds hgY1 hv'
        have hres := mem_sub (mem_fastFxx hg hu' hv')
          (mem_mul mem_cFv_21 (mem_add (mem_mul (mem_mul (mem_ofInt 2) (mem_add (mem_sq (mem_fastVP_of_guard hgX1 hu'))
            (mem_mul (mem_fastV validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2)) (mem_fastVPP_of_guard hgX hu'))))
            (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_sq (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2))) (mem_fastPhiPP_of_guard hgX hu'))))
        unfold Hxx_Fv; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fsq_eq]
        convert hres using 1; unfold Hxx_F wvPP wv_fun; push_cast; ring)
      (fun hg hu' hv' => by
        have ⟨_, _, hgX1, hgY1⟩ := guard2DFHess_extract hg
        have hu01 := fGuardD1_bounds hgX1 hu'; have hv01 := fGuardD1_bounds hgY1 hv'
        have hres := mem_sub (mem_fastFxy hg hu' hv')
          (mem_mul mem_cFv_21 (mem_add (mem_mul (mem_mul (mem_ofInt 2) (mem_mul (mem_fastV validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2)) (mem_fastVP_of_guard hgX1 hu')))
            (mem_fastPhiP_of_guard hgY1 hv'))
            (mem_mul (mem_mul (mem_ofInt 2) (mem_mul (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastVP_of_guard hgY1 hv')))
            (mem_fastPhiP_of_guard hgX1 hu'))))
        unfold Hxy_Fv; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq]
        convert hres using 1; unfold Hxy_F wvP; push_cast; ring)
      hok hu hv huv dx dy)
    chk_Fv_b0 chk_Fv_b1 chk_Fv_b2 chk_Fv_b3 chk_Fv_b4 chk_Fv_b5 chk_Fv_b6 chk_Fv_b7
  intro x y hx0 hx1 hy0 hy1; simpa using h x y hx0 hx1 hy0 hy1

/-! ### 3. `cert_F_sim` -/

theorem cert_F_sim : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    (3 / 100 : ℝ) * (phi x * R_fun y + phi y * R_fun x)
    + (13 / 100 : ℝ) * (v_fun x ^ 2 * phi y + v_fun y ^ 2 * phi x) ≤ F_fun x y :=
  cert_F_combo (a := 3 / 100) (b := 13 / 100) (ok := okFsim) (okH := okFsimHess)
    (by norm_num) (by norm_num) (by norm_num)
    (by unfold p01_Fsim SCALE; norm_num) (by unfold p99999_Fsim SCALE; norm_num)
    (by decide) (by decide) (by decide) (by decide)
    (fun w X Y hok u v hu hv huv => okF_sound (a := 3 / 100) (b := 13 / 100) (G_iv := G_Fsim) (Gx_iv := Gx_Fsim)
      (fun hg hIlo hIhi hJlo hJhi hu' hv' => by
        have ⟨hgX, hgY⟩ := guard2DF_extract hg
        have hu01 := sub_box_bounds hgX hIlo hIhi hu'; have hv01 := sub_box_bounds hgY hJlo hJhi hv'
        unfold G_Fsim G_F wv_fun; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fsq_eq, fastF_of_eq, fastR_of_eq, fastV_of_eq]
        exact mem_sub (mem_sub (mem_fastF validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2) hv' (le_of_lt hv01.1) (le_of_lt hv01.2))
          (mem_mul mem_cFsim_3 (mem_add (mem_mul (mem_fastPhi validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2)) (mem_fastR validConstIv qL_lo_pos hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastR validConstIv qL_lo_pos hu' (le_of_lt hu01.1) (le_of_lt hu01.2))))))
          (mem_mul mem_cFsim_13 (mem_add (mem_mul (mem_sq (mem_fastV validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2))) (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_sq (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2))) (mem_fastPhi validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2))))))
      (fun hg hu' hv' => by
        have ⟨hgX, hgY⟩ := guard2DF_extract hg
        have hu01 := fGuardD1_bounds hgX hu'; have hv01 := fGuardD1_bounds hgY hv'
        have hres := mem_sub (mem_sub (mem_fastFx hg hu' hv')
          (mem_mul mem_cFsim_3 (mem_add (mem_mul (mem_fastPhiP_of_guard hgX hu') (mem_fastR validConstIv qL_lo_pos hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastRP_of_guard hgX hu')))))
          (mem_mul mem_cFsim_13 (mem_add (mem_mul (mem_mul (mem_ofInt 2) (mem_mul (mem_fastV validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2)) (mem_fastVP_of_guard hgX hu')))
            (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_sq (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2))) (mem_fastPhiP_of_guard hgX hu'))))
        unfold Gx_Fsim; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fsq_eq, fastFx_of_eq, fastR_of_eq, fastRP_of_eq, fastV_of_eq, fastVP_of_eq]
        convert hres using 1; unfold Gx_F wvP wv_fun; push_cast; ring)
      (fun hg hlo hhi hv' => by
        have ⟨hgX, hgY⟩ := guard2DF_extract hg
        have hmx01 := fGuardD1_bounds hgX (mem_sub_pt_le hlo hhi _ (mem_pt _)); have hv01 := fGuardD1_bounds hgY hv'
        have hres := mem_sub (mem_sub (mem_fastFx_pt hg hlo hhi hv')
          (mem_mul mem_cFsim_3 (mem_add (mem_mul (mem_fastPhiP_of_guard hgY hv') (mem_fastR validConstIv qL_lo_pos (mem_pt _) (le_of_lt hmx01.1) (le_of_lt hmx01.2)))
            (mem_mul (mem_fastPhi validConstIv (mem_pt _) (le_of_lt hmx01.1) (le_of_lt hmx01.2)) (mem_fastRP_of_guard hgY hv')))))
          (mem_mul mem_cFsim_13 (mem_add (mem_mul (mem_mul (mem_ofInt 2) (mem_mul (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastVP_of_guard hgY hv')))
            (mem_fastPhi validConstIv (mem_pt _) (le_of_lt hmx01.1) (le_of_lt hmx01.2)))
            (mem_mul (mem_sq (mem_fastV validConstIv (mem_pt _) (le_of_lt hmx01.1) (le_of_lt hmx01.2))) (mem_fastPhiP_of_guard hgY hv'))))
        unfold Gx_Fsim; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fsq_eq, fastFx_of_eq, fastR_of_eq, fastRP_of_eq, fastV_of_eq, fastVP_of_eq]
        convert hres using 1; unfold Gx_F wvP wv_fun; push_cast; ring)
      hok hu hv huv)
    (fun w X Y hok u v hu hv huv dx dy => okFHess_sound (a := 3 / 100) (b := 13 / 100) (Hxx_iv := Hxx_Fsim) (Hxy_iv := Hxy_Fsim)
      (fun hg hu' hv' => by
        have ⟨hgX, _, hgX1, hgY1⟩ := guard2DFHess_extract hg
        have hu01 := fGuardD1_bounds hgX1 hu'; have hv01 := fGuardD1_bounds hgY1 hv'
        have hres := mem_sub (mem_sub (mem_fastFxx hg hu' hv')
          (mem_mul mem_cFsim_3 (mem_add (mem_mul (mem_fastPhiPP_of_guard hgX hu') (mem_fastR validConstIv qL_lo_pos hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastRPP_of_guard hgX hu')))))
          (mem_mul mem_cFsim_13 (mem_add (mem_mul (mem_mul (mem_ofInt 2) (mem_add (mem_sq (mem_fastVP_of_guard hgX1 hu'))
            (mem_mul (mem_fastV validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2)) (mem_fastVPP_of_guard hgX hu'))))
            (mem_fastPhi validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)))
            (mem_mul (mem_sq (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2))) (mem_fastPhiPP_of_guard hgX hu'))))
        unfold Hxx_Fsim; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq, fsq_eq]
        convert hres using 1; unfold Hxx_F wvPP wv_fun; push_cast; ring)
      (fun hg hu' hv' => by
        have ⟨_, _, hgX1, hgY1⟩ := guard2DFHess_extract hg
        have hu01 := fGuardD1_bounds hgX1 hu'; have hv01 := fGuardD1_bounds hgY1 hv'
        have hres := mem_sub (mem_sub (mem_fastFxy hg hu' hv')
          (mem_mul mem_cFsim_3 (mem_add (mem_mul (mem_fastPhiP_of_guard hgX1 hu') (mem_fastRP_of_guard hgY1 hv'))
            (mem_mul (mem_fastPhiP_of_guard hgY1 hv') (mem_fastRP_of_guard hgX1 hu')))))
          (mem_mul mem_cFsim_13 (mem_add (mem_mul (mem_mul (mem_ofInt 2) (mem_mul (mem_fastV validConstIv hu' (le_of_lt hu01.1) (le_of_lt hu01.2)) (mem_fastVP_of_guard hgX1 hu')))
            (mem_fastPhiP_of_guard hgY1 hv'))
            (mem_mul (mem_mul (mem_ofInt 2) (mem_mul (mem_fastV validConstIv hv' (le_of_lt hv01.1) (le_of_lt hv01.2)) (mem_fastVP_of_guard hgY1 hv')))
            (mem_fastPhiP_of_guard hgX1 hu'))))
        unfold Hxy_Fsim; simp only [ivCBV_eq, fsub_eq, fmul_eq, fadd_eq]
        convert hres using 1; unfold Hxy_F wvP; push_cast; ring)
      hok hu hv huv dx dy)
    chk_Fsim_b0 chk_Fsim_b1 chk_Fsim_b2 chk_Fsim_b3 chk_Fsim_b4 chk_Fsim_b5 chk_Fsim_b6 chk_Fsim_b7

end UCBound.Cert2D
