module

public import UCBound.Cert2DHelpers
public import UCBound.CertStripTrees
public import UCBound.Cert1D

@[expose] public section

/-!
# Certified Boundary Strips for 2D Inequalities (`F_R`, `F_v`, `F_sim`)

Proves the 4 fast-log 1D helper inequalities and analytic boundary strips so that
the 2D certificate module (`CertF`) only needs to cover compact interior boxes:
- `cert_v_sq_le_phi`: `v_fun x ^ 2 ≤ (9/100) * phi x` on `[0, 1]`
- `cert_F_strip_low` / `cert_F_strip_high`: unified strip `B(x, y) + phi x * AR_fun y ≥ 0`
  for `x ≤ 1/100` or `x ≥ 99999/100000` (covers all 3 of `hF_R`, `hF_v`, `hF_sim`).
-/

namespace UCBound.Cert2D

open UCBound UCBound.Iv UCBound.Cert UCBound.FastIv

/-! ### Interval Predicates & 4 FastLog Kernel-Checked 1D Trees -/

def c9_100 : Interval := ofRat 9 100
def c11_200 : Interval := ofRat 11 200

def ARIv (X : Interval) : Interval :=
  ivCBV X fun X =>
  ivCBV (fastH X) fun hX => ivCBV (fastPhi constIv X) fun phX =>
  fsub (fmul (fsub qLIv c11_200) phX) (fmul c11_200 (fastR_of constIv X hX phX))

def okVsqPhi (X : Interval) : Bool :=
  ivCBV X fun X =>
  decide (0 < X.lo) && decide (X.hi < SCALE) &&
  ivCBV (fastH X) fun hX => ivCBV (fastPhi constIv X) fun phX =>
  decide (0 < (fsub (fmul c9_100 phX) (fsq (fastV_of constIv hX phX))).lo)

def okARLow (X : Interval) : Bool :=
  ivCBV X fun X =>
  decide (0 < X.lo) && decide (0 < (fsub ONE X).lo) &&
  decide (0 < (fadd (fmul (ofRat 9 2) (ARIv X)) (fmul (fsub ONE X) (fastLog (fsub ONE X)))).lo)

def okARY (X : Interval) : Bool :=
  ivCBV X fun X =>
  decide (0 < X.lo) && decide (X.hi < SCALE) &&
  decide (0 < (fsub (ARIv X) (fmul (ofRat 1 20) X)).lo)

def okARSqrt (X : Interval) : Bool :=
  ivCBV X fun X =>
  decide (0 < X.lo) && decide (0 ≤ (fsub ONE X).lo) && decide (X.hi < SCALE) &&
  decide (0 < (fsub (ARIv X) (fmul (ofRat 26 100) (fastSqrt (fsub ONE X)))).lo)

set_option maxRecDepth 200000 in set_option maxHeartbeats 8000000 in
lemma chk_VsqPhi : check1D okVsqPhi s001 s999 treeVsqPhi = true := by decide +kernel

set_option maxRecDepth 200000 in set_option maxHeartbeats 8000000 in
lemma chk_ARLow : check1D okARLow s001 s999 treeARLow = true := by decide +kernel

set_option maxRecDepth 200000 in set_option maxHeartbeats 8000000 in
lemma chk_ARY : check1D okARY s001 s95Hi treeARY = true := by decide +kernel

set_option maxRecDepth 200000 in set_option maxHeartbeats 8000000 in
lemma chk_ARSqrt : check1D okARSqrt s95Lo s99999 treeARSqrt = true := by decide +kernel

/-! ### Elementary Certified Constants and Sharp Endpoint Bounds -/

private lemma mem_c9_100 : mem c9_100 (9 / 100 : ℝ) := by unfold c9_100; simpa using mem_ofRat (p := 9) (q := 100) (by norm_num)
private lemma mem_c11_200 : mem c11_200 (11 / 200 : ℝ) := by unfold c11_200; simpa using mem_ofRat (p := 11) (q := 200) (by norm_num)

private lemma s_L_gt : (693 / 1000 : ℝ) < L := by
  have ht : mem (ofRat 693 1000) (693 / 1000 : ℝ) := by convert mem_ofRat (p := 693) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo ht mem_LN2 (by decide)

private lemma s_L_lt : L < (694 / 1000 : ℝ) := by
  have ht : mem (ofRat 694 1000) (694 / 1000 : ℝ) := by convert mem_ofRat (p := 694) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo mem_LN2 ht (by decide)

private lemma s_qL_gt : (162 / 1000 : ℝ) < qStar * L := by
  have ht : mem (ofRat 162 1000) (162 / 1000 : ℝ) := by convert mem_ofRat (p := 162) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo ht mem_qLIv (by decide)

private lemma s_tau_gt : (45 / 100 : ℝ) < tau := by
  have ht : mem (ofRat 45 100) (45 / 100 : ℝ) := by convert mem_ofRat (p := 45) (q := 100) (by norm_num)
  exact lt_of_hi_lt_lo ht validConstIv.htau_mem (by decide)

private lemma s_hr_lt : hr < (62 / 100 : ℝ) := by
  have ht : mem (ofRat 62 100) (62 / 100 : ℝ) := by convert mem_ofRat (p := 62) (q := 100) (by norm_num)
  exact lt_of_hi_lt_lo validConstIv.hhr_mem ht (by decide)

private lemma neg_log_144_1e6 : (884 / 100 : ℝ) < -Real.log (144 / 1000000 : ℝ) := by
  have h1 : mem (ofRat 144 1000000) (144 / 1000000 : ℝ) := by convert mem_ofRat (p := 144) (q := 1000000) (by norm_num)
  have ht : mem (ofRat 884 100) (884 / 100 : ℝ) := by convert mem_ofRat (p := 884) (q := 100) (by norm_num)
  exact lt_of_hi_lt_lo ht (mem_neg (mem_fastLog h1 (by decide))) (by decide)

private lemma neg_log_144_1e8 : (1345 / 100 : ℝ) < -Real.log (144 / 100000000 : ℝ) := by
  have h1 : mem (ofRat 144 100000000) (144 / 100000000 : ℝ) := by convert mem_ofRat (p := 144) (q := 100000000) (by norm_num)
  have ht : mem (ofRat 1345 100) (1345 / 100 : ℝ) := by convert mem_ofRat (p := 1345) (q := 100) (by norm_num)
  exact lt_of_hi_lt_lo ht (mem_neg (mem_fastLog h1 (by decide))) (by decide)

private lemma neg_log_1000_lt : -Real.log (1 / 1000 : ℝ) < (691 / 100 : ℝ) := by
  have h1 : mem (ofRat 1 1000) (1 / 1000 : ℝ) := by simpa using mem_ofRat (p := 1) (q := 1000) (by norm_num)
  have ht : mem (ofRat 691 100) (691 / 100 : ℝ) := by convert mem_ofRat (p := 691) (q := 100) (by norm_num)
  exact lt_of_hi_lt_lo (mem_neg (mem_fastLog h1 (by decide))) ht (by decide)

private lemma neg_log_100000_lt : -Real.log (1 / 100000 : ℝ) < (1152 / 100 : ℝ) := by
  have h1 : mem (ofRat 1 100000) (1 / 100000 : ℝ) := by simpa using mem_ofRat (p := 1) (q := 100000) (by norm_num)
  have ht : mem (ofRat 1152 100) (1152 / 100 : ℝ) := by convert mem_ofRat (p := 1152) (q := 100) (by norm_num)
  exact lt_of_hi_lt_lo (mem_neg (mem_fastLog h1 (by decide))) ht (by decide)

private lemma h_1_500_lt : h (1 / 500 : ℝ) < (15 / 1000 : ℝ) := by
  have h1 : mem (ofRat 1 500) (1 / 500 : ℝ) := by simpa using mem_ofRat (p := 1) (q := 500) (by norm_num)
  have ht : mem (ofRat 15 1000) (15 / 1000 : ℝ) := by convert mem_ofRat (p := 15) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo (mem_fastH h1 (by norm_num) (by norm_num)) ht (by decide)

/-- Sharp lower bound `h u ≥ u * (-Real.log u + 99/100)` for `u ∈ (0, 1/100]`. -/
private lemma h_ge_mul_neg_log_add {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 100) :
    u * (-Real.log u + 99 / 100) ≤ h u := by
  have hlog : Real.log (1 - u) ≤ -u := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 - u by linarith); linarith
  have h1 : (99 / 100 : ℝ) * u ≤ -(1 - u) * Real.log (1 - u) := by nlinarith
  unfold h; linarith

/-- Sharp lower bound `phi x ≥ (9/2) * x` for `x ∈ (0, 1/100]`. -/
private lemma phi_ge_9_2_x {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 100) :
    (9 / 2 : ℝ) * x ≤ phi x := by
  have hI_ge : (144 / 100 : ℝ) * x ^ 2 ≤ I_fun x x := by
    unfold I_fun
    have h1 : (144 / 100 : ℝ) ≤ 1 + tau * (1 - x) * (1 - x) := by
      have : (99 / 100 : ℝ) ^ 2 ≤ (1 - x) * (1 - x) := by nlinarith
      nlinarith [s_tau_gt]
    have h2 : x * x = x ^ 2 := by ring
    rw [h2]; nlinarith [sq_nonneg x]
  have hI_le : I_fun x x ≤ 1 / 2 := by
    unfold I_fun
    have : 1 + tau * (1 - x) * (1 - x) ≤ 3 / 2 := by nlinarith [tau_pos, tau_lt_half, sq_nonneg (1 - x)]
    nlinarith [sq_nonneg x]
  set u := (144 / 100 : ℝ) * x ^ 2
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 144 / 1000000 := by simp only [u]; nlinarith
  have hh_ge : h u ≤ h (I_fun x x) :=
    h_monotoneOn_left ⟨le_of_lt hu0, by linarith⟩ ⟨le_trans (le_of_lt hu0) hI_ge, hI_le⟩ hI_ge
  have hhu := h_ge_mul_neg_log_add hu0 (by linarith)
  have hlog : (884 / 100 : ℝ) ≤ -Real.log u := by
    have := Real.log_le_log hu0 hu1; linarith [neg_log_144_1e6]
  have hsq : ((9 / 2 : ℝ) * x) ^ 2 ≤ h (I_fun x x) / L := by
    rw [le_div_iff₀ L_pos]
    have : (144 / 100 : ℝ) * (884 / 100 + 99 / 100) * x ^ 2 ≤ h (I_fun x x) := by
      have h1' : u * (884 / 100 + 99 / 100) ≤ h u := by nlinarith
      simp only [u] at h1' hh_ge; linarith
    nlinarith [s_L_lt, sq_nonneg x]
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity)] at this

/-- Tighter lower bound `phi x ≥ 5 * x` for `x ∈ (0, 1/1000]`. -/
private lemma phi_ge_5_x {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 1000) :
    (5 : ℝ) * x ≤ phi x := by
  have hI_ge : (144 / 100 : ℝ) * x ^ 2 ≤ I_fun x x := by
    unfold I_fun
    have h1 : (144 / 100 : ℝ) ≤ 1 + tau * (1 - x) * (1 - x) := by
      have : (99 / 100 : ℝ) ^ 2 ≤ (1 - x) * (1 - x) := by nlinarith
      nlinarith [s_tau_gt]
    have h2 : x * x = x ^ 2 := by ring
    rw [h2]; nlinarith [sq_nonneg x]
  have hI_le : I_fun x x ≤ 1 / 2 := by
    unfold I_fun
    have : 1 + tau * (1 - x) * (1 - x) ≤ 3 / 2 := by nlinarith [tau_pos, tau_lt_half, sq_nonneg (1 - x)]
    nlinarith [sq_nonneg x]
  set u := (144 / 100 : ℝ) * x ^ 2
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 144 / 100000000 := by simp only [u]; nlinarith
  have hh_ge : h u ≤ h (I_fun x x) :=
    h_monotoneOn_left ⟨le_of_lt hu0, by linarith⟩ ⟨le_trans (le_of_lt hu0) hI_ge, hI_le⟩ hI_ge
  have hhu := h_ge_mul_neg_log_add hu0 (by linarith)
  have hlog : (1345 / 100 : ℝ) ≤ -Real.log u := by
    have := Real.log_le_log hu0 hu1; linarith [neg_log_144_1e8]
  have hsq : ((5 : ℝ) * x) ^ 2 ≤ h (I_fun x x) / L := by
    rw [le_div_iff₀ L_pos]
    have : (144 / 100 : ℝ) * (1345 / 100 + 99 / 100) * x ^ 2 ≤ h (I_fun x x) := by
      have h1' : u * (1345 / 100 + 99 / 100) ≤ h u := by nlinarith
      simp only [u] at h1' hh_ge; linarith
    nlinarith [s_L_lt, sq_nonneg x]
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity)] at this

/-! ### 1. `cert_v_sq_le_phi` -/

theorem cert_v_sq_le_phi : ∀ x, 0 ≤ x → x ≤ 1 → v_fun x ^ 2 ≤ (9 / 100 : ℝ) * phi x := by
  intro x hx0 hx1
  rcases hx0.eq_or_lt with rfl | hx_pos
  · unfold v_fun phi I_fun; simp [h_zero]
  rcases hx1.eq_or_lt with rfl | hx_lt
  · unfold v_fun phi I_fun; simp [h_one]
  by_cases h1 : x ≤ (s001 : ℝ) / SCALE
  · have hx001 : x ≤ 1 / 1000 := by
      have : (s001 : ℝ) / SCALE ≤ 1 / 1000 := by unfold s001 SCALE; norm_num
      linarith
    have hphi_lb := phi_ge_5_x hx_pos hx001
    have hphi_ub : phi x ≤ 2 / 10 := by
      have hI_le : I_fun x x ≤ 1 / 500 := by
        unfold I_fun
        have : 1 + tau * (1 - x) * (1 - x) ≤ 3 / 2 := by nlinarith [tau_pos, tau_lt_half, sq_nonneg (1 - x)]
        nlinarith [sq_nonneg x]
      have hh := h_monotoneOn_left ⟨le_of_lt (I_fun_self_pos hx_pos hx_lt), by linarith⟩ ⟨by norm_num, by norm_num⟩ hI_le
      have hsq : h (I_fun x x) / L ≤ (2 / 10 : ℝ) ^ 2 := by
        rw [div_le_iff₀ L_pos]; linarith [h_1_500_lt, s_L_gt]
      have := Real.sqrt_le_sqrt hsq; rwa [Real.sqrt_sq (by norm_num)] at this
    have hh_ub : h x ≤ (26 / 100 : ℝ) * Real.sqrt x := by
      have h1' := h_le_mul_one_sub_log (x := x) (by linarith)
      have h2' := sqrt_mul_neg_log_le hx_pos hx001 (by norm_num)
      have hsq1000 : Real.sqrt (1 / 1000 : ℝ) ≤ 32 / 1000 := by
        have h : (1 / 1000 : ℝ) ≤ (32 / 1000 : ℝ) ^ 2 := by norm_num
        have := Real.sqrt_le_sqrt h; rwa [Real.sqrt_sq (by norm_num)] at this
      have h3' : Real.sqrt x * (1 - Real.log x) ≤ 26 / 100 := by
        have hsqx : Real.sqrt x ≤ 32 / 1000 := le_trans (Real.sqrt_le_sqrt hx001) hsq1000
        have : Real.sqrt x * (-Real.log x) ≤ (32 / 1000 : ℝ) * (691 / 100) := by
          have := neg_log_1000_lt; nlinarith [Real.sqrt_nonneg (1 / 1000 : ℝ)]
        linarith
      have heq : x * (1 - Real.log x) = Real.sqrt x * (Real.sqrt x * (1 - Real.log x)) := by
        rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt hx_pos)]
      rw [heq] at h1'; nlinarith [Real.sqrt_nonneg x]
    have hv_sq : v_fun x ^ 2 ≤ max (h x ^ 2) ((hr * phi x) ^ 2) := by
      unfold v_fun
      have ha : 0 ≤ h x := h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt)
      have hb : 0 ≤ hr * phi x := mul_nonneg (h_nonneg (le_of_lt rStar_pos) (le_of_lt rStar_lt_one)) (phi_nonneg x)
      rcases le_total (h x) (hr * phi x) with hle | hle
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)
    have hcase1 : h x ^ 2 ≤ (9 / 100 : ℝ) * phi x := by
      have : h x ^ 2 ≤ ((26 / 100 : ℝ) * Real.sqrt x) ^ 2 :=
        pow_le_pow_left₀ (h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt)) hh_ub 2
      rw [mul_pow, Real.sq_sqrt (le_of_lt hx_pos)] at this
      linarith
    have hcase2 : (hr * phi x) ^ 2 ≤ (9 / 100 : ℝ) * phi x := by
      have hhr0 : 0 ≤ hr := h_nonneg (le_of_lt rStar_pos) (le_of_lt rStar_lt_one)
      have h1' : hr ^ 2 * phi x ≤ (62 / 100 : ℝ) ^ 2 * (2 / 10) := by
        nlinarith [s_hr_lt, phi_nonneg x]
      have : (hr * phi x) ^ 2 = (hr ^ 2 * phi x) * phi x := by ring
      rw [this]; nlinarith [phi_nonneg x]
    exact le_trans hv_sq (max_le hcase1 hcase2)
  · push Not at h1
    by_cases h2 : x ≤ (s999 : ℝ) / SCALE
    · exact le_of_lt (sub_pos.mp (check1D_sound (P := fun u => 0 < (9 / 100 : ℝ) * phi u - v_fun u ^ 2)
        (fun X hok u hu => by
          unfold okVsqPhi at hok; simp only [ivCBV_eq, fsub_eq, fmul_eq, fsq_eq, fastV_of_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
          have hu0 := pos_of_lo_pos hu hok.1.1
          have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by rw [div_lt_one SCALE_pos]; exact_mod_cast hok.1.2)
          exact pos_of_lo_pos (mem_sub (mem_mul mem_c9_100 (mem_fastPhi validConstIv hu (le_of_lt hu0) (le_of_lt hu1)))
            (mem_sq (mem_fastV validConstIv hu (le_of_lt hu0) (le_of_lt hu1)))) hok.2)
        chk_VsqPhi ⟨le_of_lt h1, h2⟩))
    · push Not at h2
      set a := 1 - x
      have ha0 : 0 < a := by linarith
      have ha1 : a ≤ 1 / 1000 := by
        have : 999 / 1000 ≤ (s999 : ℝ) / SCALE := by unfold s999 SCALE; norm_num
        linarith
      have hphi_lb : (42 / 10 : ℝ) * Real.sqrt a ≤ phi x := by
        have := phi_ge_near_one ha0 ha1; simpa [a] using this
      have hphi_ub : phi x ≤ 2 / 10 := by
        have hI_ge : 1 - 2 * a ≤ I_fun x x := by
          unfold I_fun
          have h1' : 0 ≤ tau * (1 - x) * (1 - x) := by rw [mul_assoc, ← _root_.sq]; exact mul_nonneg (le_of_lt tau_pos) (sq_nonneg _)
          nlinarith [sq_nonneg a]
        have hh := h_antitoneOn_right ⟨by linarith, by linarith⟩ ⟨by linarith, le_of_lt (I_fun_self_lt_one hx_pos hx_lt)⟩ hI_ge
        rw [h_symm] at hh
        have hh2 := le_trans hh (h_monotoneOn_left ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ (by linarith : 2 * a ≤ 1 / 500))
        have hsq : h (I_fun x x) / L ≤ (2 / 10 : ℝ) ^ 2 := by
          rw [div_le_iff₀ L_pos]; linarith [h_1_500_lt, s_L_gt]
        have := Real.sqrt_le_sqrt hsq; rwa [Real.sqrt_sq (by norm_num)] at this
      have hh_ub : h x ≤ (26 / 100 : ℝ) * Real.sqrt a := by
        rw [← h_symm x, show 1 - x = a from rfl]
        have h1' := h_le_mul_one_sub_log (x := a) (by linarith)
        have h2' := sqrt_mul_neg_log_le ha0 ha1 (by norm_num)
        have hsq1000 : Real.sqrt (1 / 1000 : ℝ) ≤ 32 / 1000 := by
          have h : (1 / 1000 : ℝ) ≤ (32 / 1000 : ℝ) ^ 2 := by norm_num
          have := Real.sqrt_le_sqrt h; rwa [Real.sqrt_sq (by norm_num)] at this
        have h3' : Real.sqrt a * (1 - Real.log a) ≤ 26 / 100 := by
          have hsqa : Real.sqrt a ≤ 32 / 1000 := le_trans (Real.sqrt_le_sqrt ha1) hsq1000
          have : Real.sqrt a * (-Real.log a) ≤ (32 / 1000 : ℝ) * (691 / 100) := by
            have := neg_log_1000_lt; nlinarith [Real.sqrt_nonneg (1 / 1000 : ℝ)]
          linarith
        have heq : a * (1 - Real.log a) = Real.sqrt a * (Real.sqrt a * (1 - Real.log a)) := by
          rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt ha0)]
        rw [heq] at h1'; nlinarith [Real.sqrt_nonneg a]
      have hv_sq : v_fun x ^ 2 ≤ max (h x ^ 2) ((hr * phi x) ^ 2) := by
        unfold v_fun
        have ha' : 0 ≤ h x := h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt)
        have hb' : 0 ≤ hr * phi x := mul_nonneg (h_nonneg (le_of_lt rStar_pos) (le_of_lt rStar_lt_one)) (phi_nonneg x)
        rcases le_total (h x) (hr * phi x) with hle | hle
        · exact le_trans (by nlinarith) (le_max_right _ _)
        · exact le_trans (by nlinarith) (le_max_left _ _)
      have hcase1 : h x ^ 2 ≤ (9 / 100 : ℝ) * phi x := by
        have : h x ^ 2 ≤ ((26 / 100 : ℝ) * Real.sqrt a) ^ 2 :=
          pow_le_pow_left₀ (h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt)) hh_ub 2
        rw [mul_pow, Real.sq_sqrt (le_of_lt ha0)] at this
        have ha_le_sq : a ≤ Real.sqrt a := by
          have : Real.sqrt a ≤ 1 := by
            have := Real.sqrt_le_sqrt (show a ≤ 1 by linarith); rwa [Real.sqrt_one] at this
          nlinarith [Real.mul_self_sqrt (le_of_lt ha0), Real.sqrt_nonneg a]
        nlinarith [Real.sqrt_nonneg a]
      have hcase2 : (hr * phi x) ^ 2 ≤ (9 / 100 : ℝ) * phi x := by
        have hhr0 : 0 ≤ hr := h_nonneg (le_of_lt rStar_pos) (le_of_lt rStar_lt_one)
        have h1' : hr ^ 2 * phi x ≤ (62 / 100 : ℝ) ^ 2 * (2 / 10) := by nlinarith [s_hr_lt, phi_nonneg x]
        have : (hr * phi x) ^ 2 = (hr ^ 2 * phi x) * phi x := by ring
        rw [this]; nlinarith [phi_nonneg x]
      exact le_trans hv_sq (max_le hcase1 hcase2)

/-! ### 2. Unified Boundary Strip for `F_R`, `F_v`, `F_sim` -/

noncomputable def B_fun (x y : ℝ) : ℝ := h (x * y) - y * h x - x * h y

noncomputable def AR_fun (y : ℝ) : ℝ :=
  (qStar * L - 11 / 200) * phi y - (11 / 200) * R_fun y

private lemma AR_ge_52_phi {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (52 / 1000 : ℝ) * phi y ≤ AR_fun y := by
  unfold AR_fun
  have := cert_R_le_phi y hy0 hy1
  nlinarith [s_qL_gt, phi_nonneg y]

private lemma mem_ARIv {Y : Interval} {y : ℝ} (hy : mem Y y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    mem (ARIv Y) (AR_fun y) := by
  unfold ARIv; simp only [ivCBV_eq, fsub_eq, fmul_eq, fastR_of_eq]
  exact mem_sub (mem_mul (mem_sub mem_qLIv mem_c11_200) (mem_fastPhi validConstIv hy hy0 hy1))
    (mem_mul mem_c11_200 (mem_fastR validConstIv qL_lo_pos hy hy0 hy1))

theorem cert_F_strip_low :
    ∀ x y, 0 ≤ x → x ≤ 1 / 100 → 0 ≤ y → y ≤ 1 → 0 ≤ B_fun x y + phi x * AR_fun y := by
  intro x y hx0 hx1 hy0 hy1
  rcases hx0.eq_or_lt with rfl | hx_pos
  · unfold B_fun phi I_fun; simp [h_zero]
  rcases hy0.eq_or_lt with rfl | hy_pos
  · unfold B_fun AR_fun R_fun F_fun phi I_fun; simp [h_zero]
  rcases hy1.eq_or_lt with rfl | hy_lt
  · unfold B_fun AR_fun R_fun F_fun phi I_fun; simp [h_one]
  have hB := B_ge_x_om_y_log (le_of_lt hx_pos) (by linarith) (le_of_lt hy_pos) (le_of_lt hy_lt)
  have hphi := phi_ge_9_2_x hx_pos hx1
  have hAR_nn : 0 ≤ AR_fun y := le_trans (mul_nonneg (by norm_num) (phi_nonneg y)) (AR_ge_52_phi (le_of_lt hy_pos) (le_of_lt hy_lt))
  suffices hmain : 0 ≤ (9 / 2 : ℝ) * AR_fun y + (1 - y) * Real.log (1 - y) by
    have h1 : (9 / 2 : ℝ) * x * AR_fun y ≤ phi x * AR_fun y := mul_le_mul_of_nonneg_right hphi hAR_nn
    have h2 : 0 ≤ x * ((9 / 2 : ℝ) * AR_fun y + (1 - y) * Real.log (1 - y)) := mul_nonneg (le_of_lt hx_pos) hmain
    unfold B_fun; linarith
  by_cases h1 : y ≤ (s001 : ℝ) / SCALE
  · have hy001 : y ≤ 1 / 1000 := by
      have : (s001 : ℝ) / SCALE ≤ 1 / 1000 := by unfold s001 SCALE; norm_num
      linarith
    have hAR_lb : (52 / 1000 : ℝ) * ((9 / 2) * y) ≤ AR_fun y :=
      le_trans (mul_le_mul_of_nonneg_left (phi_ge_9_2_x hy_pos (by linarith)) (by norm_num)) (AR_ge_52_phi (le_of_lt hy_pos) (le_of_lt hy_lt))
    have hlog : -y ≤ (1 - y) * Real.log (1 - y) := by
      have h1my : 0 < 1 - y := by linarith
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1my)
      rw [Real.log_inv] at this
      have hmul : (1 - y) * (-Real.log (1 - y)) ≤ (1 - y) * ((1 - y)⁻¹ - 1) :=
        mul_le_mul_of_nonneg_left this (le_of_lt h1my)
      have heq : (1 - y) * ((1 - y)⁻¹ - 1) = y := by field_simp [ne_of_gt h1my]; ring
      linarith
    linarith
  · push Not at h1
    by_cases h2 : y ≤ (s999 : ℝ) / SCALE
    · exact le_of_lt (check1D_sound (P := fun u => 0 < (9 / 2 : ℝ) * AR_fun u + (1 - u) * Real.log (1 - u))
        (fun Y hok u hu => by
          unfold okARLow at hok; simp only [ivCBV_eq, fadd_eq, fsub_eq, fmul_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
          have hu0 := pos_of_lo_pos hu hok.1.1
          have hu1 := pos_of_lo_pos (mem_sub mem_ONE hu) hok.1.2
          have h92 : mem (ofRat 9 2) (9 / 2 : ℝ) := by convert mem_ofRat (p := 9) (q := 2) (by norm_num)
          exact pos_of_lo_pos (mem_add (mem_mul h92 (mem_ARIv hu (le_of_lt hu0) (by linarith)))
            (mem_mul (mem_sub mem_ONE hu) (mem_fastLog (mem_sub mem_ONE hu) hok.1.2))) hok.2)
        chk_ARLow ⟨le_of_lt h1, h2⟩)
    · push Not at h2
      set a := 1 - y
      have ha0 : 0 < a := by linarith
      have ha1 : a ≤ 1 / 1000 := by
        have : 999 / 1000 ≤ (s999 : ℝ) / SCALE := by unfold s999 SCALE; norm_num
        linarith
      have hphi_y : (42 / 10 : ℝ) * Real.sqrt a ≤ phi y := by
        have := phi_ge_near_one ha0 ha1; simpa [a] using this
      have hAR_lb := le_trans (mul_le_mul_of_nonneg_left hphi_y (by norm_num)) (AR_ge_52_phi (le_of_lt hy_pos) (le_of_lt hy_lt))
      have hlog : a * (-Real.log a) ≤ (23 / 100 : ℝ) * Real.sqrt a := by
        have h2' := sqrt_mul_neg_log_le ha0 ha1 (by norm_num)
        have hsq1000 : Real.sqrt (1 / 1000 : ℝ) ≤ 32 / 1000 := by
          have h : (1 / 1000 : ℝ) ≤ (32 / 1000 : ℝ) ^ 2 := by norm_num
          have := Real.sqrt_le_sqrt h; rwa [Real.sqrt_sq (by norm_num)] at this
        have h3' : Real.sqrt a * (-Real.log a) ≤ 23 / 100 := by
          have := neg_log_1000_lt; nlinarith [Real.sqrt_nonneg (1 / 1000 : ℝ)]
        have heq : a * (-Real.log a) = Real.sqrt a * (Real.sqrt a * (-Real.log a)) := by
          rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt ha0)]
        rw [heq]; nlinarith [Real.sqrt_nonneg a]
      have ha_eq : (1 - y) * Real.log (1 - y) = -(a * (-Real.log a)) := by simp only [a]; ring
      rw [ha_eq]; nlinarith [Real.sqrt_nonneg a]

theorem cert_F_strip_high :
    ∀ x y, 99999 / 100000 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ B_fun x y + phi x * AR_fun y := by
  intro x y hx1 hx2 hy0 hy1
  have hx_pos : 0 < x := by linarith
  rcases hx2.eq_or_lt with rfl | hx_lt
  · unfold B_fun phi I_fun; simp [h_one]
  rcases hy0.eq_or_lt with rfl | hy_pos
  · unfold B_fun AR_fun R_fun F_fun phi I_fun; simp [h_zero]
  rcases hy1.eq_or_lt with rfl | hy_lt
  · unfold B_fun AR_fun R_fun F_fun phi I_fun; simp [h_one]
  set a := 1 - x
  have ha0 : 0 < a := by linarith
  have ha1 : a ≤ 1 / 100000 := by linarith
  have hphi_x : (57 / 10 : ℝ) * Real.sqrt a ≤ phi x := by
    have := phi_ge_near_one_1e5 ha0 ha1; simpa [a] using this
  have ha_log : a * (-Real.log a) ≤ (37 / 1000 : ℝ) * Real.sqrt a := by
    have h1 := sqrt_mul_neg_log_le ha0 ha1 (by norm_num)
    have hsq_ub : Real.sqrt (1 / 100000 : ℝ) ≤ 317 / 100000 := by
      have h : (1 / 100000 : ℝ) ≤ (317 / 100000 : ℝ) ^ 2 := by norm_num
      have := Real.sqrt_le_sqrt h; rwa [Real.sqrt_sq (by norm_num)] at this
    have h3 : Real.sqrt a * (-Real.log a) ≤ 37 / 1000 := by
      have := neg_log_100000_lt; nlinarith [Real.sqrt_nonneg (1 / 100000 : ℝ)]
    have heq : a * (-Real.log a) = Real.sqrt a * (Real.sqrt a * (-Real.log a)) := by
      rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt ha0)]
    rw [heq]; nlinarith [Real.sqrt_nonneg a]
  by_cases hy95 : y ≤ (s95Hi : ℝ) / SCALE
  · have hB := B_ge_y_om_x_log (le_of_lt hx_pos) (le_of_lt hx_lt) (le_of_lt hy_pos) (le_of_lt hy_lt)
    have hAR_y : (1 / 20 : ℝ) * y ≤ AR_fun y := by
      by_cases hy001 : y ≤ (s001 : ℝ) / SCALE
      · have hy' : y ≤ 1 / 1000 := by
          have : (s001 : ℝ) / SCALE ≤ 1 / 1000 := by unfold s001 SCALE; norm_num
          linarith
        have := le_trans (mul_le_mul_of_nonneg_left (phi_ge_9_2_x hy_pos (by linarith)) (by norm_num))
          (AR_ge_52_phi (le_of_lt hy_pos) (le_of_lt hy_lt))
        linarith
      · push Not at hy001
        exact le_of_lt (sub_pos.mp (check1D_sound (P := fun u => 0 < AR_fun u - (1 / 20 : ℝ) * u)
          (fun Y hok u hu => by
            unfold okARY at hok; simp only [ivCBV_eq, fsub_eq, fmul_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
            have hu0 := pos_of_lo_pos hu hok.1.1
            have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by rw [div_lt_one SCALE_pos]; exact_mod_cast hok.1.2)
            have h120 : mem (ofRat 1 20) (1 / 20 : ℝ) := by simpa using mem_ofRat (p := 1) (q := 20) (by norm_num)
            exact pos_of_lo_pos (mem_sub (mem_ARIv hu (le_of_lt hu0) (le_of_lt hu1)) (mem_mul h120 hu)) hok.2)
          chk_ARY ⟨le_of_lt hy001, hy95⟩))
    have h1 : (57 / 10 : ℝ) * Real.sqrt a * ((1 / 20 : ℝ) * y) ≤ phi x * AR_fun y :=
      mul_le_mul hphi_x hAR_y (by positivity) (phi_nonneg x)
    have h2 : -y * (a * (-Real.log a)) ≤ B_fun x y := by unfold B_fun; simp only [a]; linarith
    have h3 : y * (a * (-Real.log a)) ≤ y * ((37 / 1000 : ℝ) * Real.sqrt a) :=
      mul_le_mul_of_nonneg_left ha_log (le_of_lt hy_pos)
    nlinarith [Real.sqrt_nonneg a]
  · push Not at hy95
    have hB := B_ge_neg_two_L_sqrt (le_of_lt hx_pos) (le_of_lt hx_lt) (le_of_lt hy_pos) (le_of_lt hy_lt)
    have hsq_mul : Real.sqrt ((1 - x) * (1 - y)) = Real.sqrt a * Real.sqrt (1 - y) :=
      Real.sqrt_mul (le_of_lt ha0) (1 - y)
    by_cases hy99999 : y ≤ (s99999 : ℝ) / SCALE
    · have hy95Lo : (s95Lo : ℝ) / SCALE ≤ y := by
        have : s95Lo ≤ s95Hi := by decide
        linarith [div_le_div_of_nonneg_right (by exact_mod_cast this : (s95Lo : ℝ) ≤ s95Hi) (le_of_lt SCALE_pos)]
      have hAR_y : (26 / 100 : ℝ) * Real.sqrt (1 - y) ≤ AR_fun y :=
        le_of_lt (sub_pos.mp (check1D_sound (P := fun u => 0 < AR_fun u - (26 / 100 : ℝ) * Real.sqrt (1 - u))
          (fun Y hok u hu => by
            unfold okARSqrt at hok; simp only [ivCBV_eq, fsub_eq, fmul_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
            have hu0 := pos_of_lo_pos hu hok.1.1.1
            have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by rw [div_lt_one SCALE_pos]; exact_mod_cast hok.1.2)
            have h26 : mem (ofRat 26 100) (26 / 100 : ℝ) := by convert mem_ofRat (p := 26) (q := 100) (by norm_num)
            exact pos_of_lo_pos (mem_sub (mem_ARIv hu (le_of_lt hu0) (le_of_lt hu1))
              (mem_mul h26 (mem_fastSqrt (mem_sub mem_ONE hu) (by linarith)))) hok.2)
          chk_ARSqrt ⟨hy95Lo, hy99999⟩))
      have h1 : (57 / 10 : ℝ) * Real.sqrt a * ((26 / 100 : ℝ) * Real.sqrt (1 - y)) ≤ phi x * AR_fun y :=
        mul_le_mul hphi_x hAR_y (by positivity) (phi_nonneg x)
      rw [hsq_mul] at hB
      have hprod_nn : 0 ≤ Real.sqrt a * Real.sqrt (1 - y) := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg (1 - y))
      have hL2 : 2 * L * (Real.sqrt a * Real.sqrt (1 - y)) ≤ 2 * (694 / 1000 : ℝ) * (Real.sqrt a * Real.sqrt (1 - y)) :=
        mul_le_mul_of_nonneg_right (by linarith [s_L_lt]) hprod_nn
      have h1' : (57 / 10 * (26 / 100) : ℝ) * (Real.sqrt a * Real.sqrt (1 - y)) ≤ phi x * AR_fun y := by
        linarith [h1, show (57 / 10 : ℝ) * Real.sqrt a * ((26 / 100 : ℝ) * Real.sqrt (1 - y)) = (57 / 10 * (26 / 100) : ℝ) * (Real.sqrt a * Real.sqrt (1 - y)) by ring]
      unfold B_fun; linarith
    · push Not at hy99999
      set b := 1 - y
      have hb0 : 0 < b := by linarith
      have hb1 : b ≤ 1 / 100000 := by
        have : 99999 / 100000 ≤ (s99999 : ℝ) / SCALE := by unfold s99999 SCALE; norm_num
        linarith
      have hphi_y : (57 / 10 : ℝ) * Real.sqrt b ≤ phi y := by
        have := phi_ge_near_one_1e5 hb0 hb1; simpa [b] using this
      have hAR_y := le_trans (mul_le_mul_of_nonneg_left hphi_y (by norm_num)) (AR_ge_52_phi (le_of_lt hy_pos) (le_of_lt hy_lt))
      have h1 : (57 / 10 : ℝ) * Real.sqrt a * ((52 / 1000 : ℝ) * ((57 / 10 : ℝ) * Real.sqrt b)) ≤ phi x * AR_fun y :=
        mul_le_mul hphi_x hAR_y (by positivity) (phi_nonneg x)
      rw [hsq_mul] at hB
      have hB' : -(2 * L * (Real.sqrt a * Real.sqrt b)) ≤ B_fun x y := by unfold B_fun; linarith
      have hprod_nn : 0 ≤ Real.sqrt a * Real.sqrt b := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
      have hL2 : 2 * L * (Real.sqrt a * Real.sqrt b) ≤ 2 * (694 / 1000 : ℝ) * (Real.sqrt a * Real.sqrt b) :=
        mul_le_mul_of_nonneg_right (by linarith [s_L_lt]) hprod_nn
      have h1' : (57 / 10 * (52 / 1000) * (57 / 10) : ℝ) * (Real.sqrt a * Real.sqrt b) ≤ phi x * AR_fun y := by
        linarith [h1, show (57 / 10 : ℝ) * Real.sqrt a * ((52 / 1000 : ℝ) * ((57 / 10 : ℝ) * Real.sqrt b)) = (57 / 10 * (52 / 1000) * (57 / 10) : ℝ) * (Real.sqrt a * Real.sqrt b) by ring]
      linarith

end UCBound.Cert2D
