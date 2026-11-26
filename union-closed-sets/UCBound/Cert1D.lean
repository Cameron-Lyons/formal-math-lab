module

public import UCBound.AnalyticBounds
public import UCBound.Cert1DTrees

@[expose] public section

/-!
# Certified 1D Local Inequalities (All 7 Univariate Fields of `LocalInequalities`)

Proves with pure kernel `decide` (13 tiny centered-form / 2nd-derivative trees,
zero `native_decide`, zero `sorry`) plus short analytic endpoint bounds:
- `cert_R_le_phi` (re-exported from `AnalyticBounds`)
- `cert_R_nonneg`
- `cert_Signed`
- `cert_b_mem`
- `cert_Line1`
- `cert_SqrtLB`
- `cert_Bopp2D`
-/

namespace UCBound.Cert

open UCBound UCBound.Iv

/-! ### Common Positivity Guards for Interval Derivative Evaluators -/

private lemma mem_hrOverPIv : mem hrOverPIv (hr / pStar) := by
  rw [show hrOverPIv = divNeg constIv.hr constIv.p by decide]
  exact mem_divNeg validConstIv.hhr_mem validConstIv.hp_mem (by decide)

private lemma constIv_p_hi_neg : constIv.p.hi < 0 := by decide
private lemma qL_lo_pos : 0 < (mul constIv.q LN2).lo := by decide

/-- Guard checking all domain positivity preconditions needed for `phiPIv` and `RPIv` on `X`. -/
def guardD1 (X : Interval) : Bool :=
  decide (0 < X.lo) && decide (X.lo ≤ X.hi) && decide (0 < (sub ONE X).lo) &&
  decide (0 < (mul constIv.r X).lo) && decide (0 < (sub ONE (mul constIv.r X)).lo) &&
  decide (0 < (IxxIv constIv X).lo) && decide (0 < (sub ONE (IxxIv constIv X)).lo) &&
  decide (0 < (mul (mul (ofInt 2) LN2) (phiIv constIv X)).lo)

/-- Guard checking all domain positivity preconditions needed for 2nd derivatives (`phiPPIv`, `RPPIv`). -/
def guardD2 (X : Interval) : Bool :=
  guardD1 X &&
  decide (0 < (mul X (sub ONE X)).lo) &&
  decide (0 < (mul (mul constIv.r X) (sub ONE (mul constIv.r X))).lo) &&
  decide (0 < (mul (IxxIv constIv X) (sub ONE (IxxIv constIv X))).lo)

private lemma guardD1_bounds {X : Interval} (hg : guardD1 X = true) {x : ℝ} (hx : mem X x) :
    0 < x ∧ x < 1 := by
  unfold guardD1 at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  have hx0 : 0 < x := pos_of_lo_pos hx hg.1.1.1.1.1.1.1
  have h1mx : 0 < 1 - x := pos_of_lo_pos (mem_sub mem_ONE hx) hg.1.1.1.1.1.2
  exact ⟨hx0, by linarith⟩

private lemma mem_phiPIv_of_guard {X : Interval} (hg : guardD1 X = true) {x : ℝ} (hx : mem X x) :
    mem (phiPIv X) (phiP x) := by
  have ⟨hx0, hx1⟩ := guardD1_bounds hg hx
  unfold guardD1 at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  exact mem_phiPIv hx (le_of_lt hx0) (le_of_lt hx1) hg.1.1.2 hg.1.2 hg.2

private lemma mem_RPIv_of_guard {X : Interval} (hg : guardD1 X = true) {x : ℝ} (hx : mem X x) :
    mem (RPIv X) (RP x) := by
  have ⟨hx0, hx1⟩ := guardD1_bounds hg hx
  unfold guardD1 at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  exact mem_RPIv hx (le_of_lt hx0) (le_of_lt hx1)
    hg.1.1.1.1.1.1.1 hg.1.1.1.1.1.2 hg.1.1.1.1.2 hg.1.1.1.2 hg.1.1.2 hg.1.2 hg.2

private lemma mem_vPIv_of_guard {X : Interval} (hg : guardD1 X = true) {x : ℝ} (hx : mem X x) :
    mem (vPIv X) (vP x) := by
  have hphi := mem_phiPIv_of_guard hg hx
  unfold guardD1 at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  exact mem_sub (mem_hpIv hx hg.1.1.1.1.1.1.1 hg.1.1.1.1.1.2) (mem_mul validConstIv.hhr_mem hphi)

private lemma mem_bPIv_of_guard {X : Interval} (hg : guardD1 X = true) {x : ℝ} (hx : mem X x) :
    mem (bPIv X) (bP x) := by
  have hphi := mem_phiPIv_of_guard hg hx
  unfold guardD1 at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  exact mem_sub (mem_sub mem_ONE (mem_divNeg (mem_hpIv hx hg.1.1.1.1.1.1.1 hg.1.1.1.1.1.2)
    validConstIv.hp_mem constIv_p_hi_neg)) (mem_mul validConstIv.hc_mem hphi)

private lemma mem_RPPIv_of_guard {X : Interval} (hg : guardD2 X = true) {x : ℝ} (hx : mem X x) :
    mem (RPPIv X) (RPP x) := by
  unfold guardD2 at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  have ⟨hx0, hx1⟩ := guardD1_bounds hg.1.1.1 hx
  have hg1 := hg.1.1.1; unfold guardD1 at hg1; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg1
  exact mem_RPPIv hx (le_of_lt hx0) (le_of_lt hx1) hg.1.1.2 hg.1.2 hg1.1.1.2 hg1.1.2 hg.2 hg1.2

private lemma mem_phiPPIv_of_guard {X : Interval} (hg : guardD2 X = true) {x : ℝ} (hx : mem X x) :
    mem (phiPPIv X) (phiPP x) := by
  unfold guardD2 at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  have ⟨hx0, hx1⟩ := guardD1_bounds hg.1.1.1 hx
  have hg1 := hg.1.1.1; unfold guardD1 at hg1; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg1
  exact mem_phiPPIv hx (le_of_lt hx0) (le_of_lt hx1) hg1.1.1.2 hg1.1.2 hg.2 hg1.2

private lemma mem_vPPIv_of_guard {X : Interval} (hg : guardD2 X = true) {x : ℝ} (hx : mem X x) :
    mem (vPPIv X) (vPP x) := by
  have hphi := mem_phiPPIv_of_guard hg hx
  unfold guardD2 at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  exact mem_sub (mem_hppIv hx hg.1.1.2) (mem_mul validConstIv.hhr_mem hphi)

private lemma mem_bPPIv_of_guard {X : Interval} (hg : guardD2 X = true) {x : ℝ} (hx : mem X x) :
    mem (bPPIv X) (bPP x) := by
  have hphi := mem_phiPPIv_of_guard hg hx
  unfold guardD2 at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  exact mem_sub (mem_neg (mem_divNeg (mem_hppIv hx hg.1.1.2) validConstIv.hp_mem constIv_p_hi_neg))
    (mem_mul validConstIv.hc_mem hphi)

/-! ### 1D Leaf Checkers (Bit-for-Bit Mirror of `Cert1DTrees.lean`) -/

def signedIv (X : Interval) : Interval :=
  add (sub (mul (sub X constIv.r) (hIv X)) (mul hrOverPIv (vIv constIv X))) (RIv constIv X)
def signedPIv (X : Interval) : Interval :=
  add (sub (add (hIv X) (mul (sub X constIv.r) (hpIv X))) (mul hrOverPIv (vPIv X))) (RPIv X)
def signedPPIv (X : Interval) : Interval :=
  add (sub (add (mul (ofInt 2) (hpIv X)) (mul (sub X constIv.r) (hppIv X))) (mul hrOverPIv (vPPIv X))) (RPPIv X)

def line1Iv (X : Interval) : Interval := sub (add (mul (ofRat 4 5) (phiIv constIv X)) (ofRat 27 400)) (hIv X)
def line1PIv (X : Interval) : Interval := sub (mul (ofRat 4 5) (phiPIv X)) (hpIv X)
def sqrtLBIv (X : Interval) : Interval :=
  sub (sqrt (mul X (hIv X)))
    (sub (add (mul (ofRat (-3) 50) (hIv X)) (mul (ofRat 685 1000) (phiIv constIv X))) (mul (ofRat 27 100) (RIv constIv X)))
def sqrtLBPIv (X : Interval) : Interval :=
  sub (divPos (add (hIv X) (mul X (hpIv X))) (mul (ofInt 2) (sqrt (mul X (hIv X)))))
    (sub (add (mul (ofRat (-3) 50) (hpIv X)) (mul (ofRat 685 1000) (phiPIv X))) (mul (ofRat 27 100) (RPIv X)))
def bopp1DIv (X : Interval) : Interval :=
  sub (hIv (clamp01 (sq X))) (mul (ofRat 809 500) (mul X (hIv X)))
def bopp1DPIv (X : Interval) : Interval :=
  sub (mul (ofInt 2) (mul X (hpIv (sq X)))) (mul (ofRat 809 500) (add (hIv X) (mul X (hpIv X))))

def okRpp (X : Interval) : Bool := guardD2 X && decide (0 < (RPPIv X).lo)
def okBpp (X : Interval) : Bool := guardD2 X && decide (0 < (bPPIv X).lo)
def okSpp (X : Interval) : Bool := guardD2 X && decide (0 < (signedPPIv X).lo)
def okRPos (X : Interval) : Bool := guardD1 X && centered1DPos (RIv constIv) RPIv X
def okSigned (X : Interval) : Bool := guardD1 X && centered1DPos signedIv signedPIv X
def okBPos (X : Interval) : Bool := guardD1 X && centered1DPos (bIv constIv) bPIv X
def okBLt1 (X : Interval) : Bool := decide (0 ≤ X.lo) && decide (X.hi ≤ (SCALE : ℤ)) && decide ((bIv constIv X).hi < (SCALE : ℤ))
def okLine1 (X : Interval) : Bool := guardD1 X && centered1DPos line1Iv line1PIv X
def okSqrtLB (X : Interval) : Bool :=
  guardD1 X && decide (0 < (mul (ofInt 2) (sqrt (mul X (hIv X)))).lo) && centered1DPos sqrtLBIv sqrtLBPIv X
def okBopp1D (X : Interval) : Bool :=
  decide (0 < X.lo) && decide (X.lo ≤ X.hi) && decide (0 < (sub ONE X).lo) &&
  decide (0 < (sq X).lo) && decide (0 < (sub ONE (sq X)).lo) &&
  centered1DPos bopp1DIv bopp1DPIv X

/-! ### Pure-Kernel `decide` Checks of All 13 1D Trees -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma chk_Rpp : check1D okRpp c67Lo c71Hi treeRpp = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma chk_Bpp : check1D okBpp c67Lo c71Hi treeBpp = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma chk_Spp : check1D okSpp c67Lo c71Hi treeSpp = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma chk_RPosL : check1D okRPos c01 c67Hi treeRPosL = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma chk_RPosR : check1D okRPos c71Lo c999 treeRPosR = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
lemma chk_SignedL : check1D okSigned c005 c67Hi treeSignedL = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma chk_SignedR : check1D okSigned c71Lo c999 treeSignedR = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma chk_BPosL : check1D okBPos c001 c67Hi treeBPosL = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma chk_BPosR : check1D okBPos c71Lo c999 treeBPosR = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma chk_BLt1 : check1D okBLt1 0 c999 treeBLt1 = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma chk_Line1 : check1D okLine1 c0001 c9999 treeLine1 = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
lemma chk_SqrtLB : check1D okSqrtLB c005 c999 treeSqrtLB = true := by decide
set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
lemma chk_Bopp1D : check1D okBopp1D c01 c4096 treeBopp1D = true := by decide

/-! ### Elementary Endpoint Helpers (Near `0` and Near `1`) -/

private lemma mem_rat {p : ℤ} {q : ℕ} (hq : 0 < q) (r : ℝ) (hr : (p : ℝ) / (q : ℝ) = r) :
    mem (ofRat p q) r := hr ▸ mem_ofRat p hq

private lemma c01_le : (c01 : ℝ) / SCALE ≤ 1 / 100 := by
  have := (mem_rat (p := 1) (q := 100) (by norm_num) (1 / 100) (by norm_num)).1; exact this
private lemma c005_le : (c005 : ℝ) / SCALE ≤ 1 / 200 := by
  have := (mem_rat (p := 1) (q := 200) (by norm_num) (1 / 200) (by norm_num)).1; exact this
private lemma c001_le : (c001 : ℝ) / SCALE ≤ 1 / 1000 := by
  have := (mem_rat (p := 1) (q := 1000) (by norm_num) (1 / 1000) (by norm_num)).1; exact this
private lemma c0001_le : (c0001 : ℝ) / SCALE ≤ 1 / 10000 := by
  have := (mem_rat (p := 1) (q := 10000) (by norm_num) (1 / 10000) (by norm_num)).1; exact this
private lemma c999_ge : (999 / 1000 : ℝ) ≤ (c999 : ℝ) / SCALE := by
  have := (mem_rat (p := 999) (q := 1000) (by norm_num) (999 / 1000) (by norm_num)).2; exact this
private lemma c9999_ge : (9999 / 10000 : ℝ) ≤ (c9999 : ℝ) / SCALE := by
  have := (mem_rat (p := 9999) (q := 10000) (by norm_num) (9999 / 10000) (by norm_num)).2; exact this
private lemma c67Lo_pos : (0 : ℝ) < (c67Lo : ℝ) / SCALE :=
  div_pos (by exact_mod_cast (by decide : (0 : ℤ) < c67Lo)) SCALE_pos

/-- `h` is monotone increasing on `[0, 1/2]`. -/
lemma h_monotoneOn_left : MonotoneOn h (Set.Icc (0 : ℝ) (1 / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
    (continuousOn_h.mono (Set.Icc_subset_Icc_right (by norm_num)))
  · intro x hx; rw [interior_Icc] at hx
    exact (hasDerivAt_h hx.1 (by linarith [hx.2])).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Icc] at hx
    rw [(hasDerivAt_h hx.1 (by linarith [hx.2])).deriv]
    unfold hp
    exact Real.log_nonneg (by rw [one_le_div hx.1]; linarith [hx.2])

/-- `h` is antitone decreasing on `[1/2, 1]`. -/
lemma h_antitoneOn_right : AntitoneOn h (Set.Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [← h_symm x, ← h_symm y]
  exact h_monotoneOn_left ⟨by linarith [hy.2], by linarith [hy.1]⟩
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)

/-- For `x ∈ (0, 1/100]`, `x * √(2 * (-Real.log x) / L) ≤ phi x`. -/
lemma phi_ge_small {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 100) :
    x * Real.sqrt (2 * (-Real.log x) / L) ≤ phi x := by
  have hI_ge : x ^ 2 ≤ I_fun x x := by
    unfold I_fun
    have h1 : 0 ≤ tau * (1 - x) * (1 - x) := by rw [mul_assoc, ← _root_.sq]; exact mul_nonneg (le_of_lt tau_pos) (sq_nonneg _)
    have h2 : x * x = x ^ 2 := by ring
    rw [h2]; nlinarith [sq_nonneg x]
  have hI_le : I_fun x x ≤ 1 / 2 := by
    unfold I_fun
    have h1 : 1 + tau * (1 - x) * (1 - x) ≤ 3 / 2 := by
      have := tau_lt_half; have : (1 - x) * (1 - x) ≤ 1 := by nlinarith
      nlinarith [tau_pos]
    have h2 : x * x ≤ 1 / 10000 := by nlinarith
    nlinarith [sq_nonneg x]
  have hh_ge : h (x ^ 2) ≤ h (I_fun x x) :=
    h_monotoneOn_left ⟨sq_nonneg x, by nlinarith⟩ ⟨le_trans (sq_nonneg x) hI_ge, hI_le⟩ hI_ge
  have hlog_ge : -(x ^ 2) * Real.log (x ^ 2) ≤ h (x ^ 2) :=
    neg_mul_log_le_h (sq_nonneg x) (by nlinarith)
  have hrew : -(x ^ 2) * Real.log (x ^ 2) = x ^ 2 * (2 * (-Real.log x)) := by
    rw [Real.log_pow]; push_cast; ring
  have hdiv : x ^ 2 * (2 * (-Real.log x) / L) ≤ h (I_fun x x) / L := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt L_pos)
  have hsqrt := Real.sqrt_le_sqrt hdiv
  rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq (le_of_lt hx0)] at hsqrt
  exact hsqrt

/-- For `x ∈ (0, 1/100]`, `phi x ≤ x * √((3 / 2) * (1 - Real.log ((3 / 2) * x ^ 2)) / L)`. -/
lemma phi_le_small {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 100) :
    phi x ≤ x * Real.sqrt ((3 / 2 : ℝ) * (1 - Real.log ((3 / 2) * x ^ 2)) / L) := by
  have hI_le : I_fun x x ≤ (3 / 2 : ℝ) * x ^ 2 := by
    unfold I_fun; have := tau_lt_half
    have h1 : 1 + tau * (1 - x) * (1 - x) ≤ 3 / 2 := by nlinarith [sq_nonneg (1 - x)]
    nlinarith [sq_nonneg x]
  have hI_pos : 0 < I_fun x x := I_fun_self_pos hx0 (by linarith)
  have hh_le : h (I_fun x x) ≤ h ((3 / 2 : ℝ) * x ^ 2) :=
    h_monotoneOn_left ⟨le_of_lt hI_pos, by nlinarith⟩ ⟨by positivity, by nlinarith⟩ hI_le
  have hlog_le : h ((3 / 2 : ℝ) * x ^ 2) ≤ ((3 / 2 : ℝ) * x ^ 2) * (1 - Real.log ((3 / 2) * x ^ 2)) :=
    h_le_mul_one_sub_log (by nlinarith)
  have hdiv : h (I_fun x x) / L ≤ x ^ 2 * ((3 / 2 : ℝ) * (1 - Real.log ((3 / 2) * x ^ 2)) / L) := by
    have : h (I_fun x x) ≤ x ^ 2 * ((3 / 2 : ℝ) * (1 - Real.log ((3 / 2) * x ^ 2))) := by linarith
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right this (le_of_lt L_pos)
  have hsqrt := Real.sqrt_le_sqrt hdiv
  rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq (le_of_lt hx0)] at hsqrt
  exact hsqrt

/-- Certified lower bound `-Real.log (1 / 100) > 460 / 100` (and for `1/200`, `1/1000`, `1/4096`, `1/100000`). -/
lemma neg_log_100 : (460 / 100 : ℝ) < -Real.log (1 / 100) := by
  have h1 := mem_rat (p := 1) (q := 100) (by norm_num) (1 / 100) (by norm_num)
  have ht := mem_rat (p := 460) (q := 100) (by norm_num) (460 / 100) (by norm_num)
  exact lt_of_hi_lt_lo ht (mem_neg (mem_log h1 (by decide))) (by decide)

lemma neg_log_200 : (529 / 100 : ℝ) < -Real.log (1 / 200) := by
  have h1 := mem_rat (p := 1) (q := 200) (by norm_num) (1 / 200) (by norm_num)
  have ht := mem_rat (p := 529) (q := 100) (by norm_num) (529 / 100) (by norm_num)
  exact lt_of_hi_lt_lo ht (mem_neg (mem_log h1 (by decide))) (by decide)

lemma neg_log_1000 : (690 / 100 : ℝ) < -Real.log (1 / 1000) := by
  have h1 := mem_rat (p := 1) (q := 1000) (by norm_num) (1 / 1000) (by norm_num)
  have ht := mem_rat (p := 690) (q := 100) (by norm_num) (690 / 100) (by norm_num)
  exact lt_of_hi_lt_lo ht (mem_neg (mem_log h1 (by decide))) (by decide)

lemma neg_log_100000 : (1151 / 100 : ℝ) < -Real.log (1 / 100000) := by
  have h1 := mem_rat (p := 1) (q := 100000) (by norm_num) (1 / 100000) (by norm_num)
  have ht := mem_rat (p := 1151) (q := 100) (by norm_num) (1151 / 100) (by norm_num)
  exact lt_of_hi_lt_lo ht (mem_neg (mem_log h1 (by decide))) (by decide)

/-- `t ↦ √t * (-Real.log t)` is monotone increasing on `(0, 1/8]`. -/
lemma sqrt_mul_neg_log_le {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 8) :
    Real.sqrt a * (-Real.log a) ≤ Real.sqrt b * (-Real.log b) := by
  set f : ℝ → ℝ := fun t => Real.sqrt t * (-Real.log t)
  have hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt f ((-Real.log t - 2) / (2 * Real.sqrt t)) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have hsq := (hasDerivAt_id' t).sqrt (ne_of_gt ht0)
    have hlog := (Real.hasDerivAt_log (ne_of_gt ht0)).neg
    exact (hsq.fun_mul hlog).congr_deriv (by
      have hsq_ne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht0)
      have ht_ne : t ≠ 0 := ne_of_gt ht0
      have hsq2 : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht0)
      field_simp [hsq_ne, ht_ne]
      rw [Real.sq_sqrt (le_of_lt ht0)]; simp only [Pi.neg_apply]; ring)
  have hmono : MonotoneOn f (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro t ht; exact (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Icc] at ht
      exact (hderiv t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc] at ht
      rw [(hderiv t (Set.Ioo_subset_Icc_self ht)).deriv]
      have ht0 : 0 < t := lt_of_lt_of_le ha0 (le_of_lt ht.1)
      have ht18 : t ≤ 1 / 8 := le_trans (le_of_lt ht.2) hb
      -- -log t ≥ -log(1/8) = 3 * L > 2.07 > 2!
      have hlog8 : Real.log t ≤ Real.log (1 / 8) := Real.log_le_log ht0 ht18
      have h3L : Real.log (1 / 8 : ℝ) = -(3 * L) := by
        unfold L
        have : (1 / 8 : ℝ) = (2 : ℝ) ^ (-3 : ℤ) := by norm_num
        rw [this, Real.log_zpow]; push_cast; ring
      have hL_gt : (69 / 100 : ℝ) < L := by
        have ht' : mem (ofRat 69 100) (69 / 100 : ℝ) := by convert mem_ofRat (p := 69) (q := 100) (by norm_num)
        exact lt_of_hi_lt_lo ht' mem_LN2 (by decide)
      exact div_nonneg (by linarith) (by positivity)
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Near `1`: for `a = 1 - x ∈ (0, 1/1000]`, `phi (1 - a) ≥ (42 / 10) * √a`. -/
lemma phi_ge_near_one {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 1000) :
    (42 / 10 : ℝ) * Real.sqrt a ≤ phi (1 - a) := by
  have hI_le : I_fun (1 - a) (1 - a) ≤ 1 - (199 / 100 : ℝ) * a := by
    unfold I_fun
    have h1 : 1 - (1 - a) = a := by ring
    rw [h1]
    have h2 : 1 + tau * a * a ≤ 1 + (1 / 2) * a ^ 2 := by have := tau_lt_half; nlinarith [sq_nonneg a]
    have h3 : (1 - a) * (1 - a) = 1 - 2 * a + a ^ 2 := by ring
    have ha2 : a ^ 2 ≤ a / 1000 := by nlinarith
    have ha3 : a ^ 3 ≤ a / 1000000 := by nlinarith [sq_nonneg a]
    have ha4 : a ^ 4 ≤ a / 1000000000 := by nlinarith [sq_nonneg a, sq_nonneg (a ^ 2)]
    have h4 : (1 - 2 * a + a ^ 2) * (1 + (1 / 2) * a ^ 2) ≤ 1 - (199 / 100 : ℝ) * a := by nlinarith
    rw [h3]
    exact le_trans (mul_le_mul_of_nonneg_left h2 (by nlinarith)) h4
  have hI_ge : (1 / 2 : ℝ) ≤ I_fun (1 - a) (1 - a) := by
    unfold I_fun
    have h1 : 0 ≤ tau * (1 - (1 - a)) * (1 - (1 - a)) := by rw [mul_assoc, ← _root_.sq]; exact mul_nonneg (le_of_lt tau_pos) (sq_nonneg _)
    have h2 : (1 / 2 : ℝ) ≤ (1 - a) * (1 - a) := by nlinarith
    nlinarith
  have hh_ge : h (1 - (199 / 100 : ℝ) * a) ≤ h (I_fun (1 - a) (1 - a)) :=
    h_antitoneOn_right ⟨hI_ge, le_of_lt (I_fun_self_lt_one (by linarith) (by linarith))⟩
      ⟨by linarith, by linarith⟩ hI_le
  rw [h_symm] at hh_ge
  have hlog_ge := neg_mul_log_le_h (by linarith : (0 : ℝ) ≤ (199 / 100) * a) (by linarith)
  have hlog_ub : Real.log ((199 / 100 : ℝ) * a) ≤ Real.log (199 / 100000) :=
    Real.log_le_log (by linarith) (by linarith)
  have hneg_log_lb : (621 / 100 : ℝ) < -Real.log (199 / 100000) := by
    have h1 : mem (ofRat 199 100000) (199 / 100000 : ℝ) := by convert mem_ofRat (p := 199) (q := 100000) (by norm_num)
    have ht : mem (ofRat 621 100) (621 / 100 : ℝ) := by convert mem_ofRat (p := 621) (q := 100) (by norm_num)
    exact lt_of_hi_lt_lo ht (mem_neg (mem_log h1 (by decide))) (by decide)
  have hL_ub : L < (694 / 1000 : ℝ) := by
    have ht : mem (ofRat 694 1000) (694 / 1000 : ℝ) := by convert mem_ofRat (p := 694) (q := 1000) (by norm_num)
    exact lt_of_hi_lt_lo mem_LN2 ht (by decide)
  have hsq : ((42 / 10 : ℝ) * Real.sqrt a) ^ 2 ≤ h (I_fun (1 - a) (1 - a)) / L := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt ha0), le_div_iff₀ L_pos]
    have hstep : (199 / 100 : ℝ) * (621 / 100) * a ≤ h (I_fun (1 - a) (1 - a)) := by nlinarith
    nlinarith
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity)] at this

/-- Near `1` (tight `10^{-5}` strip for `F_pos`): for `a ∈ (0, 10^{-5}]`, `phi (1 - a) ≥ (57 / 10) * √a`. -/
lemma phi_ge_near_one_1e5 {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 100000) :
    (57 / 10 : ℝ) * Real.sqrt a ≤ phi (1 - a) := by
  have hI_le : I_fun (1 - a) (1 - a) ≤ 1 - (1999 / 1000 : ℝ) * a := by
    unfold I_fun
    have h1 : 1 - (1 - a) = a := by ring
    rw [h1]
    have h2 : 1 + tau * a * a ≤ 1 + (1 / 2) * a ^ 2 := by have := tau_lt_half; nlinarith [sq_nonneg a]
    have h3 : (1 - a) * (1 - a) = 1 - 2 * a + a ^ 2 := by ring
    have ha2 : a ^ 2 ≤ a / 100000 := by nlinarith
    have ha3 : a ^ 3 ≤ a / 10000000000 := by nlinarith [sq_nonneg a]
    have ha4 : a ^ 4 ≤ a / 1000000000000000 := by nlinarith [sq_nonneg a, sq_nonneg (a ^ 2)]
    have h4 : (1 - 2 * a + a ^ 2) * (1 + (1 / 2) * a ^ 2) ≤ 1 - (1999 / 1000 : ℝ) * a := by nlinarith
    rw [h3]
    exact le_trans (mul_le_mul_of_nonneg_left h2 (by nlinarith)) h4
  have hI_ge : (1 / 2 : ℝ) ≤ I_fun (1 - a) (1 - a) := by
    unfold I_fun
    have h1 : 0 ≤ tau * (1 - (1 - a)) * (1 - (1 - a)) := by rw [mul_assoc, ← _root_.sq]; exact mul_nonneg (le_of_lt tau_pos) (sq_nonneg _)
    have h2 : (1 / 2 : ℝ) ≤ (1 - a) * (1 - a) := by nlinarith
    nlinarith
  have hh_ge : h (1 - (1999 / 1000 : ℝ) * a) ≤ h (I_fun (1 - a) (1 - a)) :=
    h_antitoneOn_right ⟨hI_ge, le_of_lt (I_fun_self_lt_one (by linarith) (by linarith))⟩
      ⟨by linarith, by linarith⟩ hI_le
  rw [h_symm] at hh_ge
  have hlog_ge := neg_mul_log_le_h (by linarith : (0 : ℝ) ≤ (1999 / 1000) * a) (by linarith)
  have hlog_ub : Real.log ((1999 / 1000 : ℝ) * a) ≤ Real.log (2 / 100000) :=
    Real.log_le_log (by linarith) (by linarith)
  have hneg_log_lb : (1081 / 100 : ℝ) < -Real.log (2 / 100000) := by
    have h1 : mem (ofRat 2 100000) (2 / 100000 : ℝ) := by convert mem_ofRat (p := 2) (q := 100000) (by norm_num)
    have ht : mem (ofRat 1081 100) (1081 / 100 : ℝ) := by convert mem_ofRat (p := 1081) (q := 100) (by norm_num)
    exact lt_of_hi_lt_lo ht (mem_neg (mem_log h1 (by decide))) (by decide)
  have hL_ub : L < (694 / 1000 : ℝ) := by
    have ht : mem (ofRat 694 1000) (694 / 1000 : ℝ) := by convert mem_ofRat (p := 694) (q := 1000) (by norm_num)
    exact lt_of_hi_lt_lo mem_LN2 ht (by decide)
  have hsq : ((57 / 10 : ℝ) * Real.sqrt a) ^ 2 ≤ h (I_fun (1 - a) (1 - a)) / L := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt ha0), le_div_iff₀ L_pos]
    -- 1.999 * 10.81 = 21.609; (5.7)^2 * 0.694 = 32.49 * 0.694 = 22.548! Wait: 21.6 < 22.548!
    -- Wait: why did supplement.tex say 57/10?! Because h(2a) = 2a * (1 - log(2a)), NOT just -2a log(2a)!
    -- Let's include the +2a * 0.999 term: -(1 - 2a) log(1 - 2a) ≥ 2a * (1 - 2a) ≥ 1.99 a!
    -- Then 1.999 * (10.81 + 0.99) = 23.588 > 22.548!!
    have hu : (1999 / 1000 : ℝ) * a ≤ 1 / 10000 := by linarith
    have h_om : (999 / 1000 : ℝ) * ((1999 / 1000 : ℝ) * a) ≤ -(1 - (1999 / 1000 : ℝ) * a) * Real.log (1 - (1999 / 1000 : ℝ) * a) := by
      set u := (1999 / 1000 : ℝ) * a
      have hu0 : 0 < u := by positivity
      have hu1 : u < 1 := by linarith
      have hlog_le := Real.log_le_sub_one_of_pos (show 0 < 1 - u by linarith)
      nlinarith
    have hfull : (1999 / 1000 : ℝ) * (1081 / 100 + 999 / 1000) * a ≤ h (I_fun (1 - a) (1 - a)) := by
      have hh_def : h ((1999 / 1000 : ℝ) * a) = -((1999 / 1000 : ℝ) * a) * Real.log ((1999 / 1000 : ℝ) * a)
          - (1 - (1999 / 1000 : ℝ) * a) * Real.log (1 - (1999 / 1000 : ℝ) * a) := rfl
      nlinarith
    nlinarith
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity)] at this

/-- Near `1`: upper bound `phi (1 - a) ≤ √(2 * a * (1 - Real.log (2 * a)) / L)` for `a ∈ (0, 1/1000]`. -/
lemma phi_le_near_one {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 1000) :
    phi (1 - a) ≤ Real.sqrt (2 * a * (1 - Real.log (2 * a)) / L) := by
  have hI_ge : 1 - 2 * a ≤ I_fun (1 - a) (1 - a) := by
    unfold I_fun
    have h1 : 0 ≤ tau * (1 - (1 - a)) * (1 - (1 - a)) := by rw [mul_assoc, ← _root_.sq]; exact mul_nonneg (le_of_lt tau_pos) (sq_nonneg _)
    have h2 : 1 - 2 * a ≤ (1 - a) * (1 - a) := by nlinarith [sq_nonneg a]
    nlinarith
  have hh_le : h (I_fun (1 - a) (1 - a)) ≤ h (1 - 2 * a) :=
    h_antitoneOn_right ⟨by linarith, by linarith⟩
      ⟨by linarith, le_of_lt (I_fun_self_lt_one (by linarith) (by linarith))⟩ hI_ge
  rw [h_symm] at hh_le
  have hlog_le := h_le_mul_one_sub_log (x := 2 * a) (by linarith)
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (le_trans hh_le hlog_le) (le_of_lt L_pos))

/-! ### Helper: Certified Constant Inequalities Used in Endpoint Strips -/

private lemma const_omr_log_omr : -(1 - rStar) * Real.log (1 - rStar) < 364 / 1000 := by
  have homr := mem_sub mem_ONE validConstIv.hr_mem
  have hlog := mem_log homr (by decide)
  have hprod := mem_neg (mem_mul homr hlog)
  have ht : mem (ofRat 364 1000) (364 / 1000 : ℝ) := by convert mem_ofRat (p := 364) (q := 1000) (by norm_num)
  have hlt := lt_of_hi_lt_lo hprod ht (by decide)
  linarith

private lemma const_qL_gt : (162 / 1000 : ℝ) < qStar * L := by
  have ht : mem (ofRat 162 1000) (162 / 1000 : ℝ) := by convert mem_ofRat (p := 162) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo ht mem_qLIv1 (by decide)

private lemma const_L_gt : (693 / 1000 : ℝ) < L := by
  have ht : mem (ofRat 693 1000) (693 / 1000 : ℝ) := by convert mem_ofRat (p := 693) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo ht mem_LN2 (by decide)

private lemma const_L_lt : L < (694 / 1000 : ℝ) := by
  have ht : mem (ofRat 694 1000) (694 / 1000 : ℝ) := by convert mem_ofRat (p := 694) (q := 1000) (by norm_num)
  exact lt_of_hi_lt_lo mem_LN2 ht (by decide)

private lemma const_rStar_lt : rStar < 7 / 10 := by
  have ht : mem (ofRat 7 10) (7 / 10 : ℝ) := by convert mem_ofRat (p := 7) (q := 10) (by norm_num)
  exact lt_of_hi_lt_lo validConstIv.hr_mem ht (by decide)

private lemma const_rStar_mem_67_71 : rStar ∈ Set.Icc ((c67Lo : ℝ) / SCALE) ((c71Hi : ℝ) / SCALE) := by
  have h1 : c67Lo < constIv.r.lo := by decide
  have h2 : constIv.r.hi < c71Hi := by decide
  have hS := SCALE_pos
  exact ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt h1) (le_of_lt hS)) validConstIv.hr_mem.1,
         le_trans validConstIv.hr_mem.2 (div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt h2) (le_of_lt hS))⟩

/-! ### 1. `cert_R_nonneg` -/

theorem cert_R_nonneg : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ R_fun x := by
  intro x hx0 hx1
  have hS := SCALE_pos
  have hqL_pos : 0 < qStar * L := by linarith [const_qL_gt]
  rcases hx0.eq_or_lt with rfl | hx_pos
  · unfold R_fun F_fun phi I_fun; simp [h_zero]
  rcases hx1.eq_or_lt with rfl | hx_lt
  · unfold R_fun F_fun phi I_fun; simp [h_one]
  -- Split into 5 intervals: (0, c01], [c01, c67Hi], [c67Lo, c71Hi], [c71Lo, c999], [c999, 1)
  by_cases h1 : x ≤ (c01 : ℝ) / SCALE
  · -- Analytic left strip x ∈ (0, 0.01]:
    have hx01 : x ≤ 1 / 100 := le_trans h1 c01_le
    have hB := B_ge_y_om_x_log (le_of_lt rStar_pos) (le_of_lt rStar_lt_one) (le_of_lt hx_pos) (le_of_lt hx_lt)
    have hphi := phi_ge_small hx_pos hx01
    have hlog_ge : (460 / 100 : ℝ) ≤ -Real.log x := by
      have := Real.log_le_log hx_pos hx01; linarith [neg_log_100]
    have hsq_ge : (36 / 10 : ℝ) ≤ Real.sqrt (2 * (-Real.log x) / L) := by
      have hsq : (36 / 10 : ℝ) ^ 2 ≤ 2 * (-Real.log x) / L := by
        rw [le_div_iff₀ L_pos]; nlinarith [const_L_lt]
      have := Real.sqrt_le_sqrt hsq; rwa [Real.sqrt_sq (by norm_num)] at this
    have hphi_lb : (36 / 10 : ℝ) * x ≤ phi x := by nlinarith
    unfold R_fun F_fun; rw [phi_rStar, mul_one]
    apply div_nonneg _ (le_of_lt hqL_pos)
    have h1' : -(364 / 1000 : ℝ) * x ≤ h (rStar * x) - x * h rStar - rStar * h x := by
      have := const_omr_log_omr; nlinarith
    have h2' : (364 / 1000 : ℝ) * x ≤ qStar * L * phi x := by nlinarith [const_qL_gt]
    linarith
  · push Not at h1
    by_cases h2 : x ≤ (c67Hi : ℝ) / SCALE
    · exact le_of_lt (check1D_sound (P := fun u => 0 < R_fun u) (fun X hok u hu => by
        unfold okRPos at hok; simp only [Bool.and_eq_true] at hok
        have hgd := hok.1
        have hXle : X.lo ≤ X.hi := by
          unfold guardD1 at hgd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd; exact hgd.1.1.1.1.1.1.2
        exact centered1DPos_sound hXle
          (fun I hlo hhi v hv => by
            have hv01 := guardD1_bounds hgd ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hv.1,
              le_trans hv.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩
            exact mem_RIv validConstIv qL_lo_pos hv (le_of_lt hv01.1) (le_of_lt hv01.2))
          (fun v hv => mem_RPIv_of_guard hgd hv)
          (fun v hv => (hasDerivAt_R (guardD1_bounds hgd ⟨hv.1, hv.2⟩).1 (guardD1_bounds hgd ⟨hv.1, hv.2⟩).2).continuousAt.continuousWithinAt)
          (fun v hv => hasDerivAt_R (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).1 (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).2)
          hok.2 hu) chk_RPosL ⟨le_of_lt h1, h2⟩)
    · push Not at h2
      by_cases h3 : x ≤ (c71Hi : ℝ) / SCALE
      · -- Double-zero convexity on [c67Lo, c71Hi]!
        have hc67 : (c67Lo : ℝ) / SCALE ≤ x := by
          have : c67Lo ≤ c67Hi := by decide
          linarith [div_le_div_of_nonneg_right (by exact_mod_cast this : (c67Lo : ℝ) ≤ c67Hi) (le_of_lt hS)]
        have hpp_pos : ∀ u ∈ Set.Icc ((c67Lo : ℝ) / SCALE) ((c71Hi : ℝ) / SCALE), 0 < RPP u := fun u hu =>
          check1D_sound (P := fun v => 0 < RPP v) (fun X hok v hv => by
            unfold okRpp at hok; simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
            exact pos_of_lo_pos (mem_RPPIv_of_guard hok.1 hv) hok.2) chk_Rpp ⟨hu.1, hu.2⟩
        have hI01 : ∀ u ∈ Set.Icc ((c67Lo : ℝ) / SCALE) ((c71Hi : ℝ) / SCALE), 0 < u ∧ u < 1 := fun u hu => by
          have hhi : (c71Hi : ℝ) / SCALE < 1 := by rw [div_lt_one hS]; unfold c71Hi SCALE; norm_num
          exact ⟨lt_of_lt_of_le c67Lo_pos hu.1, lt_of_le_of_lt hu.2 hhi⟩
        exact nonneg_of_deriv2_nonneg const_rStar_mem_67_71.1 const_rStar_mem_67_71.2
          (fun u hu => (hasDerivAt_R (hI01 u hu).1 (hI01 u hu).2).continuousAt.continuousWithinAt)
          (fun u hu => hasDerivAt_R (hI01 u (Set.Ioo_subset_Icc_self hu)).1 (hI01 u (Set.Ioo_subset_Icc_self hu)).2)
          (fun u hu => (hasDerivAt_RP (hI01 u hu).1 (hI01 u hu).2).continuousAt.continuousWithinAt)
          (fun u hu => hasDerivAt_RP (hI01 u (Set.Ioo_subset_Icc_self hu)).1 (hI01 u (Set.Ioo_subset_Icc_self hu)).2)
          (fun u hu => le_of_lt (hpp_pos u (Set.Ioo_subset_Icc_self hu)))
          contact_derivs.2.1 contact_derivs.2.2.1 x ⟨hc67, h3⟩
      · push Not at h3
        by_cases h4 : x ≤ (c999 : ℝ) / SCALE
        · have hc71 : (c71Lo : ℝ) / SCALE ≤ x := by
            have : c71Lo ≤ c71Hi := by decide
            linarith [div_le_div_of_nonneg_right (by exact_mod_cast this : (c71Lo : ℝ) ≤ c71Hi) (le_of_lt hS)]
          exact le_of_lt (check1D_sound (P := fun u => 0 < R_fun u) (fun X hok u hu => by
            unfold okRPos at hok; simp only [Bool.and_eq_true] at hok
            have hgd := hok.1
            have hXle : X.lo ≤ X.hi := by
              unfold guardD1 at hgd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd; exact hgd.1.1.1.1.1.1.2
            exact centered1DPos_sound hXle
              (fun I hlo hhi v hv => by
                have hv01 := guardD1_bounds hgd ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hv.1,
                  le_trans hv.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩
                exact mem_RIv validConstIv qL_lo_pos hv (le_of_lt hv01.1) (le_of_lt hv01.2))
              (fun v hv => mem_RPIv_of_guard hgd hv)
              (fun v hv => (hasDerivAt_R (guardD1_bounds hgd ⟨hv.1, hv.2⟩).1 (guardD1_bounds hgd ⟨hv.1, hv.2⟩).2).continuousAt.continuousWithinAt)
              (fun v hv => hasDerivAt_R (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).1 (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).2)
              hok.2 hu) chk_RPosR ⟨hc71, h4⟩)
        · -- Analytic right strip x ∈ [0.999, 1):
          push Not at h4
          set a := 1 - x
          have ha0 : 0 < a := by linarith
          have ha1 : a ≤ 1 / 1000 := by
            have hc : (999 / 1000 : ℝ) ≤ (c999 : ℝ) / SCALE := (mem_ofRat (p := 999) (q := 1000) (by norm_num)).2
            linarith
          have hB := B_ge_x_om_y_log (le_of_lt rStar_pos) (le_of_lt rStar_lt_one) (le_of_lt hx_pos) (le_of_lt hx_lt)
          have hphi := phi_ge_near_one ha0 ha1
          have hx_eq : 1 - a = x := by simp only [a]; ring
          rw [hx_eq] at hphi
          -- -rStar * a * log a = rStar * √a * (√a * (-log a)) ≤ 0.7 * √a * (√0.001 * (-log 0.001)) ≤ 0.25 * √a
          have hml := sqrt_mul_neg_log_le ha0 ha1 (by norm_num)
          have hsq1000 : Real.sqrt (1 / 1000 : ℝ) ≤ 32 / 1000 := by
            have : (1 / 1000 : ℝ) ≤ (32 / 1000 : ℝ) ^ 2 := by norm_num
            have := Real.sqrt_le_sqrt this; rwa [Real.sqrt_sq (by norm_num)] at this
          have hlog1000_ub : -Real.log (1 / 1000 : ℝ) < 7 := by
            have h1 := mem_rat (p := 1) (q := 1000) (by norm_num) (1 / 1000) (by norm_num)
            have ht : mem (ofInt 7) (7 : ℝ) := by simpa using mem_ofInt 7
            exact lt_of_hi_lt_lo (mem_neg (mem_log h1 (by decide))) ht (by decide)
          have h1 : Real.sqrt a * (-Real.log a) ≤ (23 / 100 : ℝ) := by
            have : Real.sqrt (1 / 1000 : ℝ) * (-Real.log (1 / 1000)) ≤ (32 / 1000) * 7 := by nlinarith [Real.sqrt_nonneg (1 / 1000 : ℝ)]
            linarith
          have h2 : -(rStar * a * Real.log a) ≤ (17 / 100 : ℝ) * Real.sqrt a := by
            have hsq : a = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt (le_of_lt ha0)).symm
            have hrew : -(rStar * a * Real.log a) = rStar * Real.sqrt a * (Real.sqrt a * (-Real.log a)) := by
              calc -(rStar * a * Real.log a) = -(rStar * (Real.sqrt a * Real.sqrt a) * Real.log a) := by rw [← hsq]
                _ = rStar * Real.sqrt a * (Real.sqrt a * (-Real.log a)) := by ring
            rw [hrew]
            have h3 : rStar * Real.sqrt a ≤ (7 / 10 : ℝ) * Real.sqrt a :=
              mul_le_mul_of_nonneg_right (le_of_lt const_rStar_lt) (Real.sqrt_nonneg a)
            have hnn : 0 ≤ Real.sqrt a * (-Real.log a) := mul_nonneg (Real.sqrt_nonneg a) (by
              have := Real.log_neg ha0 (by linarith); linarith)
            nlinarith [Real.sqrt_nonneg a]
          unfold R_fun F_fun; rw [phi_rStar, mul_one]
          apply div_nonneg _ (le_of_lt hqL_pos)
          have h3 : (17 / 100 : ℝ) * Real.sqrt a ≤ qStar * L * phi x := by
            have := const_qL_gt; nlinarith [Real.sqrt_nonneg a]
          linarith

/-! ### 2. `cert_Signed` -/

theorem cert_Signed : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ (x - rStar) * h x - (hr / pStar) * v_fun x + R_fun x := by
  intro x hx0 hx1
  have hS := SCALE_pos
  set S : ℝ → ℝ := fun u => (u - rStar) * h u - (hr / pStar) * v_fun u + R_fun u
  set S' : ℝ → ℝ := fun u => (h u + (u - rStar) * hp u) - (hr / pStar) * vP u + RP u
  set S'' : ℝ → ℝ := fun u => (2 * hp u + (u - rStar) * hpp u) - (hr / pStar) * vPP u + RPP u
  have hS_deriv : ∀ u, 0 < u → u < 1 → HasDerivAt S (S' u) u := fun u hu0 hu1 => by
    have h1 : HasDerivAt (fun t => (t - rStar) * h t) (1 * h u + (u - rStar) * hp u) u :=
      ((hasDerivAt_id' u).sub_const rStar).fun_mul (hasDerivAt_h hu0 hu1)
    have h2 := (hasDerivAt_v hu0 hu1).const_mul (hr / pStar)
    have h3 := hasDerivAt_R hu0 hu1
    exact ((h1.fun_sub h2).fun_add h3).congr_deriv (by simp only [S']; ring)
  have hS'_deriv : ∀ u, 0 < u → u < 1 → HasDerivAt S' (S'' u) u := fun u hu0 hu1 => by
    have h1 := (hasDerivAt_h hu0 hu1).fun_add (((hasDerivAt_id' u).sub_const rStar).fun_mul (hasDerivAt_hp hu0 hu1))
    have h2 := (hasDerivAt_vP hu0 hu1).const_mul (hr / pStar)
    have h3 := hasDerivAt_RP hu0 hu1
    exact ((h1.fun_sub h2).fun_add h3).congr_deriv (by simp only [S'', hpp]; ring)
  rcases hx0.eq_or_lt with rfl | hx_pos
  · unfold v_fun R_fun F_fun phi I_fun; simp [h_zero]
  rcases hx1.eq_or_lt with rfl | hx_lt
  · unfold v_fun R_fun F_fun phi I_fun; simp [h_one]
  -- Useful certified constants for analytic strips:
  have hhrp_lt : hr / pStar < -(768 / 1000) := by
    have ht : mem (ofRat (-768) 1000) (-(768 / 1000) : ℝ) := by convert mem_ofRat (p := -768) (q := 1000) (by norm_num); norm_num
    exact lt_of_hi_lt_lo mem_hrOverPIv ht (by decide)
  have h1p_gt : (52 / 100 : ℝ) < 1 + hr * (hr / pStar) := by
    have hm := mem_add mem_ONE (mem_mul validConstIv.hhr_mem mem_hrOverPIv)
    have ht : mem (ofRat 52 100) (52 / 100 : ℝ) := by convert mem_ofRat (p := 52) (q := 100) (by norm_num)
    exact lt_of_hi_lt_lo ht hm (by decide)
  have hS_rew : ∀ u, S u = (u - rStar - hr / pStar) * h u + (1 + hr * (hr / pStar)) * phi u
      + (h (rStar * u) - u * h rStar - rStar * h u) / (qStar * L) := fun u => by
    simp only [S]; unfold v_fun R_fun F_fun hr; rw [phi_rStar, mul_one]
    have hq_ne : qStar ≠ 0 := ne_of_gt qStar_pos
    have hL_ne : L ≠ 0 := ne_of_gt L_pos
    field_simp [hq_ne, hL_ne, pStar_ne_zero]; ring
  by_cases h1 : x ≤ (c005 : ℝ) / SCALE
  · -- Analytic left strip x ∈ (0, 0.005]:
    have hx005 : x ≤ 1 / 200 := le_trans h1 c005_le
    have hlog_ge : (529 / 100 : ℝ) ≤ -Real.log x := by
      have := Real.log_le_log hx_pos hx005; linarith [neg_log_200]
    have hh_lb : (529 / 100 : ℝ) * x ≤ h x := by
      have := neg_mul_log_le_h (le_of_lt hx_pos) (le_of_lt hx_lt); nlinarith
    have hphi := phi_ge_small hx_pos (by linarith)
    have hsq_ge : (39 / 10 : ℝ) ≤ Real.sqrt (2 * (-Real.log x) / L) := by
      have hsq : (39 / 10 : ℝ) ^ 2 ≤ 2 * (-Real.log x) / L := by
        rw [le_div_iff₀ L_pos]; nlinarith [const_L_lt]
      have := Real.sqrt_le_sqrt hsq; rwa [Real.sqrt_sq (by norm_num)] at this
    have hphi_lb : (39 / 10 : ℝ) * x ≤ phi x := by nlinarith
    have hB := B_ge_y_om_x_log (le_of_lt rStar_pos) (le_of_lt rStar_lt_one) (le_of_lt hx_pos) (le_of_lt hx_lt)
    have hqL_pos : 0 < qStar * L := by linarith [const_qL_gt]
    have hB_div : -(225 / 100 : ℝ) * x ≤ (h (rStar * x) - x * h rStar - rStar * h x) / (qStar * L) := by
      rw [le_div_iff₀ hqL_pos]
      have h1' : -(364 / 1000 : ℝ) * x ≤ h (rStar * x) - x * h rStar - rStar * h x := by
        have := const_omr_log_omr; nlinarith
      nlinarith [const_qL_gt]
    change 0 ≤ S x; rw [hS_rew]
    have hc1 : (68 / 1000 : ℝ) ≤ x - rStar - hr / pStar := by linarith [const_rStar_lt]
    have ht1 : (35 / 100 : ℝ) * x ≤ (x - rStar - hr / pStar) * h x := by
      have := h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt); nlinarith
    have ht2 : (202 / 100 : ℝ) * x ≤ (1 + hr * (hr / pStar)) * phi x := by nlinarith [phi_nonneg x]
    linarith
  · push Not at h1
    by_cases h2 : x ≤ (c67Hi : ℝ) / SCALE
    · exact le_of_lt (check1D_sound (P := fun u => 0 < S u) (fun X hok u hu => by
        unfold okSigned at hok; simp only [Bool.and_eq_true] at hok
        have hgd := hok.1
        have hXle : X.lo ≤ X.hi := by
          unfold guardD1 at hgd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd; exact hgd.1.1.1.1.1.1.2
        exact centered1DPos_sound hXle
          (fun I hlo hhi v hv => by
            have hv01 := guardD1_bounds hgd ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hv.1,
              le_trans hv.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩
            exact mem_add (mem_sub (mem_mul (mem_sub hv validConstIv.hr_mem) (mem_hIv hv (le_of_lt hv01.1) (le_of_lt hv01.2)))
              (mem_mul mem_hrOverPIv (mem_vIv validConstIv hv (le_of_lt hv01.1) (le_of_lt hv01.2))))
              (mem_RIv validConstIv qL_lo_pos hv (le_of_lt hv01.1) (le_of_lt hv01.2)))
          (fun v hv => by
            have hv01 := guardD1_bounds hgd hv
            have hgd' := hgd; unfold guardD1 at hgd'; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd'
            exact mem_add (mem_sub (mem_add (mem_hIv hv (le_of_lt hv01.1) (le_of_lt hv01.2))
              (mem_mul (mem_sub hv validConstIv.hr_mem) (mem_hpIv hv hgd'.1.1.1.1.1.1.1 hgd'.1.1.1.1.1.2)))
              (mem_mul mem_hrOverPIv (mem_vPIv_of_guard hgd hv))) (mem_RPIv_of_guard hgd hv))
          (fun v hv => (hS_deriv v (guardD1_bounds hgd ⟨hv.1, hv.2⟩).1 (guardD1_bounds hgd ⟨hv.1, hv.2⟩).2).continuousAt.continuousWithinAt)
          (fun v hv => hS_deriv v (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).1 (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).2)
          hok.2 hu) chk_SignedL ⟨le_of_lt h1, h2⟩)
    · push Not at h2
      by_cases h3 : x ≤ (c71Hi : ℝ) / SCALE
      · have hc67 : (c67Lo : ℝ) / SCALE ≤ x := by
          have : c67Lo ≤ c67Hi := by decide
          linarith [div_le_div_of_nonneg_right (by exact_mod_cast this : (c67Lo : ℝ) ≤ c67Hi) (le_of_lt hS)]
        have hpp_pos : ∀ u ∈ Set.Icc ((c67Lo : ℝ) / SCALE) ((c71Hi : ℝ) / SCALE), 0 < S'' u := fun u hu =>
          check1D_sound (P := fun v => 0 < S'' v) (fun X hok v hv => by
            unfold okSpp at hok; simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
            have hg2 := hok.1; unfold guardD2 at hg2; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg2
            have hg1 := hg2.1.1.1; unfold guardD1 at hg1; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg1
            have hmem : mem (signedPPIv X) (S'' v) := by
              unfold signedPPIv; simp only [S'']
              have h1 := mem_add (mem_mul (mem_ofInt 2) (mem_hpIv hv hg1.1.1.1.1.1.1.1 hg1.1.1.1.1.1.2))
                (mem_mul (mem_sub hv validConstIv.hr_mem) (mem_hppIv hv hg2.1.1.2))
              have hres := mem_add (mem_sub h1 (mem_mul mem_hrOverPIv (mem_vPPIv_of_guard hok.1 hv)))
                (mem_RPPIv_of_guard hok.1 hv)
              simpa using hres
            exact pos_of_lo_pos hmem hok.2) chk_Spp ⟨hu.1, hu.2⟩
        have hI01 : ∀ u ∈ Set.Icc ((c67Lo : ℝ) / SCALE) ((c71Hi : ℝ) / SCALE), 0 < u ∧ u < 1 := fun u hu => by
          have hhi : (c71Hi : ℝ) / SCALE < 1 := by rw [div_lt_one hS]; unfold c71Hi SCALE; norm_num
          exact ⟨lt_of_lt_of_le c67Lo_pos hu.1, lt_of_le_of_lt hu.2 hhi⟩
        have hSr : S rStar = 0 := by simp only [S, sub_self, zero_mul, contact_derivs.2.2.2.1, contact_derivs.2.1]; ring
        have hS'r : S' rStar = 0 := by
          simp only [S', sub_self, zero_mul, add_zero, contact_derivs.2.2.2.2.1, contact_derivs.2.2.1]
          unfold hr; field_simp [pStar_ne_zero]; ring
        exact nonneg_of_deriv2_nonneg const_rStar_mem_67_71.1 const_rStar_mem_67_71.2
          (fun u hu => (hS_deriv u (hI01 u hu).1 (hI01 u hu).2).continuousAt.continuousWithinAt)
          (fun u hu => hS_deriv u (hI01 u (Set.Ioo_subset_Icc_self hu)).1 (hI01 u (Set.Ioo_subset_Icc_self hu)).2)
          (fun u hu => (hS'_deriv u (hI01 u hu).1 (hI01 u hu).2).continuousAt.continuousWithinAt)
          (fun u hu => hS'_deriv u (hI01 u (Set.Ioo_subset_Icc_self hu)).1 (hI01 u (Set.Ioo_subset_Icc_self hu)).2)
          (fun u hu => le_of_lt (hpp_pos u (Set.Ioo_subset_Icc_self hu))) hSr hS'r x ⟨hc67, h3⟩
      · push Not at h3
        by_cases h4 : x ≤ (c999 : ℝ) / SCALE
        · have hc71 : (c71Lo : ℝ) / SCALE ≤ x := by
            have : c71Lo ≤ c71Hi := by decide
            linarith [div_le_div_of_nonneg_right (by exact_mod_cast this : (c71Lo : ℝ) ≤ c71Hi) (le_of_lt hS)]
          exact le_of_lt (check1D_sound (P := fun u => 0 < S u) (fun X hok u hu => by
            unfold okSigned at hok; simp only [Bool.and_eq_true] at hok
            have hgd := hok.1
            have hXle : X.lo ≤ X.hi := by
              unfold guardD1 at hgd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd; exact hgd.1.1.1.1.1.1.2
            exact centered1DPos_sound hXle
              (fun I hlo hhi v hv => by
                have hv01 := guardD1_bounds hgd ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hv.1,
                  le_trans hv.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩
                exact mem_add (mem_sub (mem_mul (mem_sub hv validConstIv.hr_mem) (mem_hIv hv (le_of_lt hv01.1) (le_of_lt hv01.2)))
                  (mem_mul mem_hrOverPIv (mem_vIv validConstIv hv (le_of_lt hv01.1) (le_of_lt hv01.2))))
                  (mem_RIv validConstIv qL_lo_pos hv (le_of_lt hv01.1) (le_of_lt hv01.2)))
              (fun v hv => by
                have hv01 := guardD1_bounds hgd hv
                have hgd' := hgd; unfold guardD1 at hgd'; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd'
                exact mem_add (mem_sub (mem_add (mem_hIv hv (le_of_lt hv01.1) (le_of_lt hv01.2))
                  (mem_mul (mem_sub hv validConstIv.hr_mem) (mem_hpIv hv hgd'.1.1.1.1.1.1.1 hgd'.1.1.1.1.1.2)))
                  (mem_mul mem_hrOverPIv (mem_vPIv_of_guard hgd hv))) (mem_RPIv_of_guard hgd hv))
              (fun v hv => (hS_deriv v (guardD1_bounds hgd ⟨hv.1, hv.2⟩).1 (guardD1_bounds hgd ⟨hv.1, hv.2⟩).2).continuousAt.continuousWithinAt)
              (fun v hv => hS_deriv v (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).1 (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).2)
              hok.2 hu) chk_SignedR ⟨hc71, h4⟩)
        · -- Analytic right strip x ∈ [0.999, 1):
          push Not at h4
          set a := 1 - x
          have ha0 : 0 < a := by linarith
          have ha1 : a ≤ 1 / 1000 := by
            have hc : (999 / 1000 : ℝ) ≤ (c999 : ℝ) / SCALE := (mem_ofRat (p := 999) (q := 1000) (by norm_num)).2
            linarith
          have hB := B_ge_x_om_y_log (le_of_lt rStar_pos) (le_of_lt rStar_lt_one) (le_of_lt hx_pos) (le_of_lt hx_lt)
          have hphi := phi_ge_near_one ha0 ha1
          have hx_eq : 1 - a = x := by simp only [a]; ring
          rw [hx_eq] at hphi
          have hml := sqrt_mul_neg_log_le ha0 ha1 (by norm_num)
          have hsq1000 : Real.sqrt (1 / 1000 : ℝ) ≤ 32 / 1000 := by
            have : (1 / 1000 : ℝ) ≤ (32 / 1000 : ℝ) ^ 2 := by norm_num
            have := Real.sqrt_le_sqrt this; rwa [Real.sqrt_sq (by norm_num)] at this
          have hlog1000_ub : -Real.log (1 / 1000 : ℝ) < 7 := by
            have h1 := mem_rat (p := 1) (q := 1000) (by norm_num) (1 / 1000) (by norm_num)
            have ht : mem (ofInt 7) (7 : ℝ) := by simpa using mem_ofInt 7
            exact lt_of_hi_lt_lo (mem_neg (mem_log h1 (by decide))) ht (by decide)
          have h2 : -(rStar * a * Real.log a) ≤ (17 / 100 : ℝ) * Real.sqrt a := by
            have hsq : a = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt (le_of_lt ha0)).symm
            have hrew : -(rStar * a * Real.log a) = rStar * Real.sqrt a * (Real.sqrt a * (-Real.log a)) := by
              calc -(rStar * a * Real.log a) = -(rStar * (Real.sqrt a * Real.sqrt a) * Real.log a) := by rw [← hsq]
                _ = rStar * Real.sqrt a * (Real.sqrt a * (-Real.log a)) := by ring
            rw [hrew]
            have h1' : Real.sqrt a * (-Real.log a) ≤ (23 / 100 : ℝ) := by nlinarith [Real.sqrt_nonneg (1 / 1000 : ℝ)]
            have hnn : 0 ≤ Real.sqrt a * (-Real.log a) := mul_nonneg (Real.sqrt_nonneg a) (by
              have := Real.log_neg ha0 (by linarith); linarith)
            have h3 : rStar * Real.sqrt a ≤ (7 / 10 : ℝ) * Real.sqrt a :=
              mul_le_mul_of_nonneg_right (le_of_lt const_rStar_lt) (Real.sqrt_nonneg a)
            nlinarith [Real.sqrt_nonneg a]
          have hqL_pos : 0 < qStar * L := by linarith [const_qL_gt]
          have hB_div : -(110 / 100 : ℝ) * Real.sqrt a ≤ (h (rStar * x) - x * h rStar - rStar * h x) / (qStar * L) := by
            rw [le_div_iff₀ hqL_pos]; nlinarith [const_qL_gt, Real.sqrt_nonneg a]
          change 0 ≤ S x; rw [hS_rew]
          have ht1 : 0 ≤ (x - rStar - hr / pStar) * h x :=
            mul_nonneg (by linarith [const_rStar_lt]) (h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt))
          have ht2 : (218 / 100 : ℝ) * Real.sqrt a ≤ (1 + hr * (hr / pStar)) * phi x := by
            nlinarith [Real.sqrt_nonneg a]
          linarith [Real.sqrt_nonneg a]

/-! ### 3. `cert_b_mem` -/

theorem cert_b_mem : ∀ x, 0 ≤ x → x ≤ 1 → 0 ≤ b_fun x ∧ b_fun x ≤ 1 := by
  intro x hx0 hx1
  have hS := SCALE_pos
  have hc_lt : cParam < (146 / 100 : ℝ) := by
    have ht : mem (ofRat 146 100) (146 / 100 : ℝ) := by convert mem_ofRat (p := 146) (q := 100) (by norm_num)
    exact lt_of_hi_lt_lo validConstIv.hc_mem ht (by decide)
  have hc_gt : (145 / 100 : ℝ) < cParam := by
    have ht : mem (ofRat 145 100) (145 / 100 : ℝ) := by convert mem_ofRat (p := 145) (q := 100) (by norm_num)
    exact lt_of_hi_lt_lo ht validConstIv.hc_mem (by decide)
  have hnp_gt : (124 / 100 : ℝ) < -(1 / pStar) := by
    have hm := mem_neg (mem_divNeg mem_ONE validConstIv.hp_mem constIv_p_hi_neg)
    have ht : mem (ofRat 124 100) (124 / 100 : ℝ) := by convert mem_ofRat (p := 124) (q := 100) (by norm_num)
    exact lt_of_hi_lt_lo ht hm (by decide)
  have hnp_lt : -(1 / pStar) < (125 / 100 : ℝ) := by
    have hm := mem_neg (mem_divNeg mem_ONE validConstIv.hp_mem constIv_p_hi_neg)
    have ht : mem (ofRat 125 100) (125 / 100 : ℝ) := by convert mem_ofRat (p := 125) (q := 100) (by norm_num)
    exact lt_of_hi_lt_lo hm ht (by decide)
  constructor
  · -- Lower bound 0 ≤ b_fun x
    rcases hx0.eq_or_lt with rfl | hx_pos
    · unfold b_fun phi I_fun; simp [h_zero]
    rcases hx1.eq_or_lt with rfl | hx_lt
    · unfold b_fun phi I_fun; simp [h_one]
    by_cases h1 : x ≤ (c001 : ℝ) / SCALE
    · have hx001 : x ≤ 1 / 1000 := le_trans h1 c001_le
      have hlog_ge : (690 / 100 : ℝ) ≤ -Real.log x := by
        have := Real.log_le_log hx_pos hx001; linarith [neg_log_1000]
      have hh_lb : -x * Real.log x ≤ h x := neg_mul_log_le_h (le_of_lt hx_pos) (le_of_lt hx_lt)
      have hphi := phi_le_small hx_pos (by linarith)
      -- 1 - log(1.5 x^2) = 1 - log(1.5) + 2(-log x) ≤ 1 + 2(-log x) ≤ (2.2) (-log x)
      have hlog15 : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
      have harg : (3 / 2 : ℝ) * (1 - Real.log ((3 / 2) * x ^ 2)) / L ≤ 5 * (-Real.log x) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (sq_pos_of_pos hx_pos)), Real.log_pow]; push_cast
        rw [div_le_iff₀ L_pos]; nlinarith [const_L_gt]
      have hphi_ub : phi x ≤ x * Real.sqrt (5 * (-Real.log x)) :=
        le_trans hphi (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt harg) (le_of_lt hx_pos))
      -- Compare: -(1/pStar) * x * (-log x) ≥ 1.24 * x * (-log x) vs cParam * x * √(5 * (-log x))!
      -- Since -log x ≥ 6.9, (1.24)^2 * (-log x) = 1.5376 * 6.9 = 10.609 > (1.46)^2 * 5 = 10.658!
      -- Include the + x term: (1 + 1.24 * (-log x))^2 ≥ (1.38 * (-log x))^2 = 1.90 * 6.9 * (-log x) = 13.1 * (-log x) > 10.66 * (-log x)!
      have hcmp : cParam * Real.sqrt (5 * (-Real.log x)) ≤ 1 + (-(1 / pStar)) * (-Real.log x) := by
        have hsq : (cParam * Real.sqrt (5 * (-Real.log x))) ^ 2 ≤ (1 + (-(1 / pStar)) * (-Real.log x)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by linarith)]
          have hc2 : cParam ^ 2 ≤ (146 / 100 : ℝ) ^ 2 := by nlinarith
          have hp1 : (124 / 100 : ℝ) * (-Real.log x) ≤ -(1 / pStar) * (-Real.log x) := by nlinarith
          nlinarith
        have := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_sq (by nlinarith [Real.sqrt_nonneg (5 * (-Real.log x))]),
             Real.sqrt_sq (by nlinarith)] at this
      unfold b_fun
      have hdiv : -(h x / pStar) = -(1 / pStar) * h x := by ring
      nlinarith
    · push Not at h1
      by_cases h2 : x ≤ (c67Hi : ℝ) / SCALE
      · exact le_of_lt (check1D_sound (P := fun u => 0 < b_fun u) (fun X hok u hu => by
          unfold okBPos at hok; simp only [Bool.and_eq_true] at hok
          have hgd := hok.1
          have hXle : X.lo ≤ X.hi := by
            unfold guardD1 at hgd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd; exact hgd.1.1.1.1.1.1.2
          exact centered1DPos_sound hXle
            (fun I hlo hhi v hv => by
              have hv01 := guardD1_bounds hgd ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hv.1,
                le_trans hv.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩
              exact mem_bIv validConstIv constIv_p_hi_neg hv (le_of_lt hv01.1) (le_of_lt hv01.2))
            (fun v hv => mem_bPIv_of_guard hgd hv)
            (fun v hv => (hasDerivAt_b (guardD1_bounds hgd ⟨hv.1, hv.2⟩).1 (guardD1_bounds hgd ⟨hv.1, hv.2⟩).2).continuousAt.continuousWithinAt)
            (fun v hv => hasDerivAt_b (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).1 (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).2)
            hok.2 hu) chk_BPosL ⟨le_of_lt h1, h2⟩)
      · push Not at h2
        by_cases h3 : x ≤ (c71Hi : ℝ) / SCALE
        · have hc67 : (c67Lo : ℝ) / SCALE ≤ x := by
            have : c67Lo ≤ c67Hi := by decide
            linarith [div_le_div_of_nonneg_right (by exact_mod_cast this : (c67Lo : ℝ) ≤ c67Hi) (le_of_lt hS)]
          have hpp_pos : ∀ u ∈ Set.Icc ((c67Lo : ℝ) / SCALE) ((c71Hi : ℝ) / SCALE), 0 < bPP u := fun u hu =>
            check1D_sound (P := fun v => 0 < bPP v) (fun X hok v hv => by
              unfold okBpp at hok; simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
              exact pos_of_lo_pos (mem_bPPIv_of_guard hok.1 hv) hok.2) chk_Bpp ⟨hu.1, hu.2⟩
          have hI01 : ∀ u ∈ Set.Icc ((c67Lo : ℝ) / SCALE) ((c71Hi : ℝ) / SCALE), 0 < u ∧ u < 1 := fun u hu => by
            have hhi : (c71Hi : ℝ) / SCALE < 1 := by rw [div_lt_one hS]; unfold c71Hi SCALE; norm_num
            exact ⟨lt_of_lt_of_le c67Lo_pos hu.1, lt_of_le_of_lt hu.2 hhi⟩
          exact nonneg_of_deriv2_nonneg const_rStar_mem_67_71.1 const_rStar_mem_67_71.2
            (fun u hu => (hasDerivAt_b (hI01 u hu).1 (hI01 u hu).2).continuousAt.continuousWithinAt)
            (fun u hu => hasDerivAt_b (hI01 u (Set.Ioo_subset_Icc_self hu)).1 (hI01 u (Set.Ioo_subset_Icc_self hu)).2)
            (fun u hu => (hasDerivAt_bP (hI01 u hu).1 (hI01 u hu).2).continuousAt.continuousWithinAt)
            (fun u hu => hasDerivAt_bP (hI01 u (Set.Ioo_subset_Icc_self hu)).1 (hI01 u (Set.Ioo_subset_Icc_self hu)).2)
            (fun u hu => le_of_lt (hpp_pos u (Set.Ioo_subset_Icc_self hu)))
            contact_derivs.2.2.2.2.2.1 contact_derivs.2.2.2.2.2.2 x ⟨hc67, h3⟩
        · push Not at h3
          by_cases h4 : x ≤ (c999 : ℝ) / SCALE
          · have hc71 : (c71Lo : ℝ) / SCALE ≤ x := by
              have : c71Lo ≤ c71Hi := by decide
              linarith [div_le_div_of_nonneg_right (by exact_mod_cast this : (c71Lo : ℝ) ≤ c71Hi) (le_of_lt hS)]
            exact le_of_lt (check1D_sound (P := fun u => 0 < b_fun u) (fun X hok u hu => by
              unfold okBPos at hok; simp only [Bool.and_eq_true] at hok
              have hgd := hok.1
              have hXle : X.lo ≤ X.hi := by
                unfold guardD1 at hgd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd; exact hgd.1.1.1.1.1.1.2
              exact centered1DPos_sound hXle
                (fun I hlo hhi v hv => by
                  have hv01 := guardD1_bounds hgd ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hv.1,
                    le_trans hv.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩
                  exact mem_bIv validConstIv constIv_p_hi_neg hv (le_of_lt hv01.1) (le_of_lt hv01.2))
                (fun v hv => mem_bPIv_of_guard hgd hv)
                (fun v hv => (hasDerivAt_b (guardD1_bounds hgd ⟨hv.1, hv.2⟩).1 (guardD1_bounds hgd ⟨hv.1, hv.2⟩).2).continuousAt.continuousWithinAt)
                (fun v hv => hasDerivAt_b (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).1 (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).2)
                hok.2 hu) chk_BPosR ⟨hc71, h4⟩)
          · push Not at h4
            -- Right strip [0.999, 1): phi(x) ≤ √(h(2a)/L) ≤ √(2*0.001*8 / 0.69) < 0.2, so x - c*phi(x) > 0.999 - 1.46*0.2 > 0!
            set a := 1 - x
            have ha0 : 0 < a := by linarith
            have ha1 : a ≤ 1 / 1000 := by
              have hc : (999 / 1000 : ℝ) ≤ (c999 : ℝ) / SCALE := (mem_ofRat (p := 999) (q := 1000) (by norm_num)).2
              linarith
            have hI_ge : 1 - 2 * a ≤ I_fun x x := by
              unfold I_fun
              have h1 : 0 ≤ tau * (1 - x) * (1 - x) := by have := tau_pos; positivity
              have h2 : 1 - 2 * a ≤ x * x := by simp only [a]; nlinarith [sq_nonneg (1 - x)]
              nlinarith
            have hh_le : h (I_fun x x) ≤ h (2 / 1000) := by
              have h1 := h_antitoneOn_right ⟨by linarith, by linarith⟩
                ⟨by linarith, le_of_lt (I_fun_self_lt_one hx_pos hx_lt)⟩ hI_ge
              rw [h_symm] at h1
              have h2 : h (2 * a) ≤ h (2 / 1000) :=
                h_monotoneOn_left ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ (by linarith)
              exact le_trans h1 h2
            have hh_2000 : h (2 / 1000 : ℝ) < 16 / 1000 := by
              have h1 : mem (ofRat 2 1000) (2 / 1000 : ℝ) := by convert mem_ofRat (p := 2) (q := 1000) (by norm_num)
              have ht : mem (ofRat 16 1000) (16 / 1000 : ℝ) := by convert mem_ofRat (p := 16) (q := 1000) (by norm_num)
              exact lt_of_hi_lt_lo (mem_hIv h1 (by norm_num) (by norm_num)) ht (by decide)
            have hphi_lt : phi x ≤ 2 / 10 := by
              unfold phi
              have hdiv : h (I_fun x x) / L ≤ (2 / 10 : ℝ) ^ 2 := by
                rw [div_le_iff₀ L_pos]; nlinarith [const_L_gt]
              have := Real.sqrt_le_sqrt hdiv; rwa [Real.sqrt_sq (by norm_num)] at this
            unfold b_fun
            have hdiv_nn : 0 ≤ -(h x / pStar) := by
              have := h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt)
              have := pStar_neg
              have : h x / pStar ≤ 0 := div_nonpos_of_nonneg_of_nonpos ‹_› (le_of_lt this)
              linarith
            nlinarith
  · -- Upper bound b_fun x ≤ 1
    by_cases h1 : x ≤ (c999 : ℝ) / SCALE
    · exact le_of_lt (check1D_sound (P := fun u => b_fun u < 1) (fun X hok u hu => by
        unfold okBLt1 at hok; simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        have hu0 : 0 ≤ u := le_trans (div_nonneg (by exact_mod_cast hok.1.1) (le_of_lt hS)) hu.1
        have hu1 : u ≤ 1 := le_trans hu.2 ((div_le_one hS).mpr (by exact_mod_cast hok.1.2))
        have hb := mem_bIv validConstIv constIv_p_hi_neg hu hu0 hu1
        have hlt : ((bIv constIv X).hi : ℝ) / SCALE < 1 := (div_lt_one hS).mpr (by exact_mod_cast hok.2)
        linarith [hb.2]) chk_BLt1 ⟨by simp [hx0], h1⟩)
    · push Not at h1
      rcases hx1.eq_or_lt with rfl | hx_lt
      · unfold b_fun phi I_fun; simp [h_one]
      set a := 1 - x
      have ha0 : 0 < a := by linarith
      have ha1 : a ≤ 1 / 1000 := by
        have hc : (999 / 1000 : ℝ) ≤ (c999 : ℝ) / SCALE := (mem_ofRat (p := 999) (q := 1000) (by norm_num)).2
        linarith
      have hphi := phi_ge_near_one ha0 ha1
      have hx_eq : 1 - a = x := by simp only [a]; ring
      rw [hx_eq] at hphi
      have hh_ub : h x ≤ 2 * L * Real.sqrt a := by
        have h1' := h_le_two_L_sqrt hx0 (le_of_lt hx_lt)
        have hsq : Real.sqrt (x * (1 - x)) ≤ Real.sqrt a :=
          Real.sqrt_le_sqrt (by nlinarith)
        nlinarith [L_pos]
      unfold b_fun
      have hdiv : -(h x / pStar) = -(1 / pStar) * h x := by ring
      have : -(1 / pStar) * h x ≤ cParam * phi x := by
        have h1' : -(1 / pStar) * h x ≤ (125 / 100 : ℝ) * (2 * L * Real.sqrt a) := by
          have := h_nonneg hx0 hx1; nlinarith [Real.sqrt_nonneg a]
        have h2' : (145 / 100 : ℝ) * ((42 / 10 : ℝ) * Real.sqrt a) ≤ cParam * phi x := by
          nlinarith [Real.sqrt_nonneg a]
        nlinarith [const_L_lt, Real.sqrt_nonneg a]
      linarith

/-! ### 4. `cert_Line1` -/

theorem cert_Line1 : ∀ x, 0 ≤ x → x ≤ 1 → h x ≤ 4 / 5 * phi x + 27 / 400 := by
  intro x hx0 hx1
  have hS := SCALE_pos
  have hh_0001 : h (1 / 10000 : ℝ) < 21 / 10000 := by
    have h1 := mem_rat (p := 1) (q := 10000) (by norm_num) (1 / 10000) (by norm_num)
    have ht := mem_rat (p := 21) (q := 10000) (by norm_num) (21 / 10000) (by norm_num)
    exact lt_of_hi_lt_lo (mem_hIv h1 (by norm_num) (by norm_num)) ht (by decide)
  by_cases h1 : x ≤ (c0001 : ℝ) / SCALE
  · have hxle : x ≤ 1 / 10000 := le_trans h1 c0001_le
    have := h_monotoneOn_left ⟨hx0, by linarith⟩ ⟨by norm_num, by norm_num⟩ hxle
    linarith [phi_nonneg x]
  · push Not at h1
    by_cases h2 : x ≤ (c9999 : ℝ) / SCALE
    · have hpos := check1D_sound (P := fun u => 0 < (4 / 5 : ℝ) * phi u + 27 / 400 - h u) (fun X hok u hu => by
        unfold okLine1 at hok; simp only [Bool.and_eq_true] at hok
        have hgd := hok.1
        have hXle : X.lo ≤ X.hi := by
          unfold guardD1 at hgd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd; exact hgd.1.1.1.1.1.1.2
        have h45 : mem (ofRat 4 5) (4 / 5 : ℝ) := by convert mem_ofRat (p := 4) (q := 5) (by norm_num)
        have h27 : mem (ofRat 27 400) (27 / 400 : ℝ) := by convert mem_ofRat (p := 27) (q := 400) (by norm_num)
        exact centered1DPos_sound hXle
          (fun I hlo hhi v hv => by
            have hv01 := guardD1_bounds hgd ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hv.1,
              le_trans hv.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩
            exact mem_sub (mem_add (mem_mul h45 (mem_phiIv validConstIv hv (le_of_lt hv01.1) (le_of_lt hv01.2))) h27)
              (mem_hIv hv (le_of_lt hv01.1) (le_of_lt hv01.2)))
          (fun v hv => by
            have hgd' := hgd; unfold guardD1 at hgd'; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd'
            exact mem_sub (mem_mul h45 (mem_phiPIv_of_guard hgd hv)) (mem_hpIv hv hgd'.1.1.1.1.1.1.1 hgd'.1.1.1.1.1.2))
          (fun v hv =>
            ((((hasDerivAt_phi (guardD1_bounds hgd ⟨hv.1, hv.2⟩).1 (guardD1_bounds hgd ⟨hv.1, hv.2⟩).2).const_mul (4 / 5)).add_const (27 / 400)).fun_sub
              (hasDerivAt_h (guardD1_bounds hgd ⟨hv.1, hv.2⟩).1 (guardD1_bounds hgd ⟨hv.1, hv.2⟩).2)).continuousAt.continuousWithinAt)
          (fun v hv =>
            (((hasDerivAt_phi (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).1 (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).2).const_mul (4 / 5)).add_const (27 / 400)).fun_sub
              (hasDerivAt_h (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).1 (guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩).2))
          hok.2 hu) chk_Line1 ⟨le_of_lt h1, h2⟩
      linarith
    · push Not at h2
      have hge : 9999 / 10000 ≤ x := le_trans (mem_ofRat (p := 9999) (q := 10000) (by norm_num)).2 (le_of_lt h2)
      rw [← h_symm x]
      have := h_monotoneOn_left ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ (by linarith : 1 - x ≤ 1 / 10000)
      linarith [phi_nonneg x]

/-! ### 5. `cert_SqrtLB` -/

theorem cert_SqrtLB : ∀ x, 0 ≤ x → x ≤ 1 →
    -(3 / 50) * h x + (685 / 1000) * phi x - (27 / 100) * R_fun x ≤ Real.sqrt (x * h x) := by
  intro x hx0 hx1
  have hS := SCALE_pos
  have hqL_pos : 0 < qStar * L := by linarith [const_qL_gt]
  rcases hx0.eq_or_lt with rfl | hx_pos
  · unfold R_fun F_fun phi I_fun; simp [h_zero]
  rcases hx1.eq_or_lt with rfl | hx_lt
  · unfold R_fun F_fun phi I_fun; simp [h_one]
  by_cases h1 : x ≤ (c005 : ℝ) / SCALE
  · -- Analytic left strip x ∈ (0, 0.005]:
    -- 685/1000 phi - 27/100 R = 415/1000 phi - (27/100)/(qL) * B(r, x)
    have hx005 : x ≤ 1 / 200 := le_trans h1 c005_le
    have hlog_ge : (529 / 100 : ℝ) ≤ -Real.log x := by
      have := Real.log_le_log hx_pos hx005; linarith [neg_log_200]
    have hsq_lb : x * Real.sqrt (-Real.log x) ≤ Real.sqrt (x * h x) := by
      have h1' : x ^ 2 * (-Real.log x) ≤ x * h x := by
        have := neg_mul_log_le_h (le_of_lt hx_pos) (le_of_lt hx_lt); nlinarith
      have := Real.sqrt_le_sqrt h1'
      rwa [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq (le_of_lt hx_pos)] at this
    have hphi := phi_le_small hx_pos (by linarith)
    have hlog15 : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
    -- (3/2) * (1 - log((3/2) x^2)) / L ≤ 4.75 * (-log x) (since 1.5*(1 + 2*5.29)/0.693 = 25.06 ≤ 4.75*5.29 = 25.13!)
    have harg : (3 / 2 : ℝ) * (1 - Real.log ((3 / 2) * x ^ 2)) / L ≤ (475 / 100 : ℝ) * (-Real.log x) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (sq_pos_of_pos hx_pos)), Real.log_pow]; push_cast
      rw [div_le_iff₀ L_pos]; nlinarith [const_L_gt]
    -- Wait: 0.415 * √4.75 = 0.415 * 2.18 = 0.905! Wait: use sharper I(x, x) ≤ 1.5 x^2 with (3/2)*2/0.693 = 4.33!
    -- Even sharper: -log(1.5) = -0.405, so 1 - log(1.5) ≤ 0.60, so 1.5 * (0.60 + 2*(-log x)) / 0.693 ≤ 4.58 * (-log x)!
    -- Wait: √(4.58) ≤ 2.141, 0.415 * 2.141 = 0.8885, leaving 0.1115 * √(-log x) ≥ 0.256 — still < 0.61!
    -- DON'T drop -(3/50) h(x)!! -(3/50) h(x) ≤ -(3/50) x (-log x) ≤ -0.317 x!
    -- AND even better: for x ≤ 0.005, 0.415 * phi(x) - 0.06 * h(x) + 0.61 * x ≤ x * √(-log x)
    -- Check at -log x = 5.29: 0.8885 * 2.30 - 0.06 * 5.29 + 0.61 = 2.043 - 0.317 + 0.61 = 2.336 vs 2.30!
    -- AHA! Why was 0.8885 too big?! Because phi(x) uses h(I) ≈ -I log I with I ≤ 1.5 x^2, so √(1.5) = 1.225!
    -- Look at h(x^2) vs h(1.5 x^2): I_fun x x = x^2 (1 + tau (1-x)^2) ≤ 1.5 x^2, so √I ≤ 1.225 x,
    -- and √(h(I)/L) ≈ 1.225 * √(2/L) * x √(-log x) = 2.08 x √(-log x) => 0.415 * 2.08 = 0.863!
    -- Check at -log x = 5.29: 0.863 * 2.30 - 0.317 + 0.61 = 2.278 < 2.30!! IT WORKS WITH -log(1.5) INCLUDED!
    -- Wait: check exact: h(1.5 x^2) ≤ 1.5 x^2 (1 - log(1.5) + 2(-log x)) ≤ 1.5 x^2 (0.6 + 2(-log x))!
    -- At u = -log x ≥ 5.29: 1.5*(0.6 + 2u)/0.693 ≤ 4.58 u; √4.58 ≤ 2.141!
    -- Wait: 0.415 * 2.141 * √u - 0.06 * u + 0.607 ≤ √u ⇔ 0.607 ≤ 0.1115 √u + 0.06 u!
    -- At u = 5.29: 0.1115 * 2.30 + 0.06 * 5.29 = 0.256 + 0.317 = 0.573 < 0.607!
    -- AHA! Why? Because we threw away `-B(r, x) ≤ (-(1-r)log(1-r)) x`? No, what IS the true bound on `-B(r, x)`?!
    -- At x → 0: -B(r, x) = r h(x) + x h(r) - h(rx) = x * (h(r) + r log r) + O(x^2) = x * (-(1-r) log(1-r))!
    -- Wait: `√(x h(x))` ALSO has `+(1-x)(-log(1-x)) ≈ x` inside `h(x)`, so `h(x) ≥ x(-log x + 0.99)`!
    -- Check √(u + 0.99) at u = 5.29: √(6.28) = 2.506!!
    -- 0.1115 * 2.506 + 0.06 * 5.29 + (2.506 - 2.30) = 0.279 + 0.317 + 0.206 = 0.802 >> 0.607!!
    -- BOOM!! Including `-(1-x) log(1-x) ≥ x (1 - x) ≥ 0.99 x` inside `h(x)` gives HUGE margin!
    have hh_tight : x * (-Real.log x + 99 / 100) ≤ h x := by
      unfold h
      have hlog1m := Real.log_le_sub_one_of_pos (show 0 < 1 - x by linarith)
      nlinarith
    have hsq_tight : x * Real.sqrt (-Real.log x + 99 / 100) ≤ Real.sqrt (x * h x) := by
      have h1' : x ^ 2 * (-Real.log x + 99 / 100) ≤ x * h x := by nlinarith
      have := Real.sqrt_le_sqrt h1'
      rwa [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq (le_of_lt hx_pos)] at this
    have hphi_ub : phi x ≤ x * ((22 / 10 : ℝ) * Real.sqrt (-Real.log x + 99 / 100)) := by
      have harg2 : (3 / 2 : ℝ) * (1 - Real.log ((3 / 2) * x ^ 2)) / L
          ≤ (22 / 10 : ℝ) ^ 2 * (-Real.log x + 99 / 100) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (sq_pos_of_pos hx_pos)), Real.log_pow]; push_cast
        rw [div_le_iff₀ L_pos]; nlinarith [const_L_gt]
      have hsq2 := Real.sqrt_le_sqrt harg2
      rw [Real.sqrt_mul (sq_nonneg (22 / 10 : ℝ)), Real.sqrt_sq (by norm_num)] at hsq2
      exact le_trans hphi (mul_le_mul_of_nonneg_left hsq2 (le_of_lt hx_pos))
    have hB := B_ge_y_om_x_log (le_of_lt rStar_pos) (le_of_lt rStar_lt_one) (le_of_lt hx_pos) (le_of_lt hx_lt)
    have hR_rew : R_fun x = phi x + (h (rStar * x) - x * h rStar - rStar * h x) / (qStar * L) := by
      unfold R_fun F_fun; rw [phi_rStar, mul_one]
      have hq_ne : qStar ≠ 0 := ne_of_gt qStar_pos
      have hL_ne : L ≠ 0 := ne_of_gt L_pos
      field_simp [hq_ne, hL_ne]; ring
    have hB_div : -(225 / 100 : ℝ) * x ≤ (h (rStar * x) - x * h rStar - rStar * h x) / (qStar * L) := by
      rw [le_div_iff₀ hqL_pos]
      have := const_omr_log_omr; nlinarith [const_qL_gt]
    have hrt_ge : (25 / 10 : ℝ) ≤ Real.sqrt (-Real.log x + 99 / 100) := by
      have hsq : (25 / 10 : ℝ) ^ 2 ≤ -Real.log x + 99 / 100 := by linarith
      have := Real.sqrt_le_sqrt hsq; rwa [Real.sqrt_sq (by norm_num)] at this
    rw [hR_rew]
    -- 0.415 * 2.2 = 0.913, so (1 - 0.913) * √(u+0.99) + 0.06*(u+0.99) ≥ 0.087*2.5 + 0.06*6.28 = 0.594 vs 0.27*2.25 = 0.6075!
    -- Use 215/100 instead of 22/10: (2.15)^2 = 4.6225, check 1.5*(1+2u)/0.693 ≤ 4.6225*(u+0.99)?
    -- 1.5*(1+2u) = 1.5 + 3u; 0.693*4.6225*(u+0.99) = 3.203*(u+0.99) = 3.203u + 3.17 >> 3u + 1.5!!
    -- Even 21/10 works: (2.1)^2 * 0.693 = 3.0561 > 3, and 3.0561 * 0.99 = 3.025 >> 1.5!
    have hphi_ub2 : phi x ≤ x * ((21 / 10 : ℝ) * Real.sqrt (-Real.log x + 99 / 100)) := by
      have harg2 : (3 / 2 : ℝ) * (1 - Real.log ((3 / 2) * x ^ 2)) / L
          ≤ (21 / 10 : ℝ) ^ 2 * (-Real.log x + 99 / 100) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (sq_pos_of_pos hx_pos)), Real.log_pow]; push_cast
        rw [div_le_iff₀ L_pos]; nlinarith [const_L_gt]
      have hsq2 := Real.sqrt_le_sqrt harg2
      rw [Real.sqrt_mul (sq_nonneg (21 / 10 : ℝ)), Real.sqrt_sq (by norm_num)] at hsq2
      exact le_trans hphi (mul_le_mul_of_nonneg_left hsq2 (le_of_lt hx_pos))
    -- 0.415 * 2.1 = 0.8715 ⇒ 0.1285 * 2.5 + 0.06 * 6.28 = 0.321 + 0.377 = 0.698 > 0.6075!
    nlinarith
  · push Not at h1
    by_cases h2 : x ≤ (c999 : ℝ) / SCALE
    · have hpos := check1D_sound
        (P := fun u => 0 < Real.sqrt (u * h u) - (-(3 / 50 : ℝ) * h u + (685 / 1000) * phi u - (27 / 100) * R_fun u))
        (fun X hok u hu => by
          unfold okSqrtLB at hok; simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
          have hgd := hok.1.1
          have hden_pos := hok.1.2
          have hXle : X.lo ≤ X.hi := by
            unfold guardD1 at hgd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd; exact hgd.1.1.1.1.1.1.2
          have ha := mem_rat (p := -3) (q := 50) (by norm_num) (-(3 / 50)) (by norm_num)
          have hb := mem_rat (p := 685) (q := 1000) (by norm_num) (685 / 1000) (by norm_num)
          have hc := mem_rat (p := 27) (q := 100) (by norm_num) (27 / 100) (by norm_num)
          exact centered1DPos_sound
            (f := fun v => Real.sqrt (v * h v) - (-(3 / 50 : ℝ) * h v + (685 / 1000) * phi v - (27 / 100) * R_fun v))
            (f' := fun v => (h v + v * hp v) / (2 * Real.sqrt (v * h v)) - (-(3 / 50 : ℝ) * hp v + (685 / 1000) * phiP v - (27 / 100) * RP v))
            hXle
            (fun I hlo hhi v hv => by
              have hv01 := guardD1_bounds hgd ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hv.1,
                le_trans hv.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩
              have hh := mem_hIv hv (le_of_lt hv01.1) (le_of_lt hv01.2)
              have hsq := mem_sqrt (mem_mul hv hh) (mul_nonneg (le_of_lt hv01.1) (h_nonneg (le_of_lt hv01.1) (le_of_lt hv01.2)))
              exact mem_sub hsq (mem_sub (mem_add (mem_mul ha hh)
                (mem_mul hb (mem_phiIv validConstIv hv (le_of_lt hv01.1) (le_of_lt hv01.2))))
                (mem_mul hc (mem_RIv validConstIv qL_lo_pos hv (le_of_lt hv01.1) (le_of_lt hv01.2)))))
            (fun v hv => by
              have hv01 := guardD1_bounds hgd hv
              have hgd' := hgd; unfold guardD1 at hgd'; simp only [Bool.and_eq_true, decide_eq_true_eq] at hgd'
              have hh := mem_hIv hv (le_of_lt hv01.1) (le_of_lt hv01.2)
              have hhp := mem_hpIv hv hgd'.1.1.1.1.1.1.1 hgd'.1.1.1.1.1.2
              have hsq := mem_sqrt (mem_mul hv hh) (mul_nonneg (le_of_lt hv01.1) (h_nonneg (le_of_lt hv01.1) (le_of_lt hv01.2)))
              have hnum := mem_add hh (mem_mul hv hhp)
              have hden := mem_mul (mem_ofInt 2) hsq
              have hq := mem_divPos hnum hden hden_pos
              have hres := mem_sub hq (mem_sub (mem_add (mem_mul ha hhp) (mem_mul hb (mem_phiPIv_of_guard hgd hv)))
                (mem_mul hc (mem_RPIv_of_guard hgd hv)))
              unfold sqrtLBPIv; simpa using hres)
            (fun v hv => by
              have hv01 := guardD1_bounds hgd ⟨hv.1, hv.2⟩
              have hvh : 0 < v * h v := mul_pos hv01.1 (h_pos hv01.1 hv01.2)
              have hd_vh : HasDerivAt (fun t => t * h t) (h v + v * hp v) v := by
                simpa using (hasDerivAt_id' v).fun_mul (hasDerivAt_h hv01.1 hv01.2)
              have hd1 := hd_vh.sqrt (ne_of_gt hvh)
              have hd2 := (((hasDerivAt_h hv01.1 hv01.2).const_mul (-(3 / 50 : ℝ))).fun_add
                ((hasDerivAt_phi hv01.1 hv01.2).const_mul (685 / 1000))).fun_sub
                ((hasDerivAt_R hv01.1 hv01.2).const_mul (27 / 100))
              exact (hd1.fun_sub hd2).continuousAt.continuousWithinAt)
            (fun v hv => by
              have hv01 := guardD1_bounds hgd ⟨le_of_lt hv.1, le_of_lt hv.2⟩
              have hvh : 0 < v * h v := mul_pos hv01.1 (h_pos hv01.1 hv01.2)
              have hd_vh : HasDerivAt (fun t => t * h t) (h v + v * hp v) v := by
                simpa using (hasDerivAt_id' v).fun_mul (hasDerivAt_h hv01.1 hv01.2)
              have hd1 := hd_vh.sqrt (ne_of_gt hvh)
              have hd2 := (((hasDerivAt_h hv01.1 hv01.2).const_mul (-(3 / 50 : ℝ))).fun_add
                ((hasDerivAt_phi hv01.1 hv01.2).const_mul (685 / 1000))).fun_sub
                ((hasDerivAt_R hv01.1 hv01.2).const_mul (27 / 100))
              exact hd1.fun_sub hd2)
            hok.2 hu) chk_SqrtLB ⟨le_of_lt h1, h2⟩
      linarith
    · -- Analytic right strip x ∈ [0.999, 1):
      push Not at h2
      set a := 1 - x
      have ha0 : 0 < a := by linarith
      have ha1 : a ≤ 1 / 1000 := by linarith [c999_ge]
      have hlog_ge : (690 / 100 : ℝ) ≤ -Real.log a := by
        have := Real.log_le_log ha0 ha1; linarith [neg_log_1000]
      have hh_a : -a * Real.log a ≤ h x := by
        rw [← h_symm x]; exact neg_mul_log_le_h (le_of_lt ha0) (by linarith)
      have hsq_lb : (99 / 100 : ℝ) * Real.sqrt a * Real.sqrt (-Real.log a) ≤ Real.sqrt (x * h x) := by
        have hsq : ((99 / 100 : ℝ) * Real.sqrt a * Real.sqrt (-Real.log a)) ^ 2 ≤ x * h x := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt ha0), Real.sq_sqrt (by linarith)]
          have h1' : (99 / 100 : ℝ) ^ 2 ≤ x := by linarith
          have h2' : 0 ≤ a * (-Real.log a) := by nlinarith
          have h3' : a * (-Real.log a) ≤ h x := by linarith
          nlinarith
        have := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_sq (by positivity)] at this
      have hphi := phi_le_near_one ha0 ha1
      have hx_eq : 1 - a = x := by simp only [a]; ring
      rw [hx_eq] at hphi
      have hphi_ub : phi x ≤ (18 / 10 : ℝ) * Real.sqrt a * Real.sqrt (-Real.log a) := by
        have h1' : 2 * a * (1 - Real.log (2 * a)) / L ≤ ((18 / 10 : ℝ) * Real.sqrt a * Real.sqrt (-Real.log a)) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt ha0), Real.sq_sqrt (by linarith),
              Real.log_mul (by norm_num) (ne_of_gt ha0), div_le_iff₀ L_pos]
          have hL_eq : Real.log 2 = L := rfl
          rw [hL_eq]
          have hc1 : 2 * (1 - L - Real.log a) ≤ (18 / 10 : ℝ) ^ 2 * L * (-Real.log a) := by
            nlinarith [const_L_gt]
          have hmul := mul_le_mul_of_nonneg_left hc1 (le_of_lt ha0)
          linarith
        have := Real.sqrt_le_sqrt h1'
        rw [Real.sqrt_sq (by positivity)] at this
        exact le_trans hphi this
      have hB := B_ge_x_om_y_log (le_of_lt rStar_pos) (le_of_lt rStar_lt_one) (le_of_lt hx_pos) (le_of_lt hx_lt)
      have hml := sqrt_mul_neg_log_le ha0 ha1 (by norm_num)
      have hsq1000 : Real.sqrt (1 / 1000 : ℝ) ≤ 32 / 1000 := by
        have : (1 / 1000 : ℝ) ≤ (32 / 1000 : ℝ) ^ 2 := by norm_num
        have := Real.sqrt_le_sqrt this; rwa [Real.sqrt_sq (by norm_num)] at this
      have hlog1000_ub : -Real.log (1 / 1000 : ℝ) < 7 := by
        have h1' := mem_rat (p := 1) (q := 1000) (by norm_num) (1 / 1000) (by norm_num)
        have ht : mem (ofInt 7) (7 : ℝ) := by simpa using mem_ofInt 7
        exact lt_of_hi_lt_lo (mem_neg (mem_log h1' (by decide))) ht (by decide)
      have hB2 : -(rStar * a * Real.log a) ≤ (17 / 100 : ℝ) * Real.sqrt a := by
        have hsq : a = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt (le_of_lt ha0)).symm
        have hrew : -(rStar * a * Real.log a) = rStar * Real.sqrt a * (Real.sqrt a * (-Real.log a)) := by
          calc -(rStar * a * Real.log a) = -(rStar * (Real.sqrt a * Real.sqrt a) * Real.log a) := by rw [← hsq]
            _ = rStar * Real.sqrt a * (Real.sqrt a * (-Real.log a)) := by ring
        rw [hrew]
        have h1' : Real.sqrt a * (-Real.log a) ≤ (23 / 100 : ℝ) := by nlinarith [Real.sqrt_nonneg (1 / 1000 : ℝ)]
        have hnn : 0 ≤ Real.sqrt a * (-Real.log a) := mul_nonneg (Real.sqrt_nonneg a) (by linarith)
        have h3 : rStar * Real.sqrt a ≤ (7 / 10 : ℝ) * Real.sqrt a :=
          mul_le_mul_of_nonneg_right (le_of_lt const_rStar_lt) (Real.sqrt_nonneg a)
        nlinarith [Real.sqrt_nonneg a]
      have hR_rew : R_fun x = phi x + (h (rStar * x) - x * h rStar - rStar * h x) / (qStar * L) := by
        unfold R_fun F_fun; rw [phi_rStar, mul_one]
        have hq_ne : qStar ≠ 0 := ne_of_gt qStar_pos
        have hL_ne : L ≠ 0 := ne_of_gt L_pos
        field_simp [hq_ne, hL_ne]; ring
      have hB_div : -(110 / 100 : ℝ) * Real.sqrt a ≤ (h (rStar * x) - x * h rStar - rStar * h x) / (qStar * L) := by
        rw [le_div_iff₀ hqL_pos]; nlinarith [const_qL_gt, Real.sqrt_nonneg a]
      have hrt_ge : (26 / 10 : ℝ) ≤ Real.sqrt (-Real.log a) := by
        have hsq : (26 / 10 : ℝ) ^ 2 ≤ -Real.log a := by linarith
        have := Real.sqrt_le_sqrt hsq; rwa [Real.sqrt_sq (by norm_num)] at this
      rw [hR_rew]
      -- 0.415 * 1.8 = 0.747; (0.99 - 0.747) * 2.6 = 0.6318 > 0.27 * 1.10 = 0.297!
      have hh_nn : 0 ≤ h x := h_nonneg (le_of_lt hx_pos) (le_of_lt hx_lt)
      nlinarith [Real.sqrt_nonneg a]

/-! ### 8. `cert_Bopp2D` -/

theorem cert_Bopp2D : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    (809 / 1000 : ℝ) * (y * h x + x * h y) ≤ h (x * y) := by
  apply bopp2D_of_bopp1D
  intro s hs0 hs1
  have hS := SCALE_pos
  rcases hs0.eq_or_lt with rfl | hs_pos
  · simp [h_zero]
  rcases hs1.eq_or_lt with rfl | hs_lt
  · simp [h_one]
  by_cases h1 : s ≤ (c01 : ℝ) / SCALE
  · -- Analytic left strip s ∈ (0, 0.01]:
    have hs01 : s ≤ 1 / 100 := le_trans h1 c01_le
    have hlog_ge : (460 / 100 : ℝ) ≤ -Real.log s := by
      have := Real.log_le_log hs_pos hs01; linarith [neg_log_100]
    have hL1 : 2 * s ^ 2 * (-Real.log s) ≤ h (s ^ 2) := by
      have := neg_mul_log_le_h (sq_nonneg s) (by nlinarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hR1 : h s ≤ s * (1 - Real.log s) := h_le_mul_one_sub_log hs_lt
    nlinarith [sq_nonneg s]
  · push Not at h1
    by_cases h2 : s ≤ (c4096 : ℝ) / SCALE
    · have hpos := check1D_sound (P := fun u => 0 < h (u ^ 2) - (809 / 500 : ℝ) * u * h u) (fun X hok u hu => by
        unfold okBopp1D at hok; simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨⟨⟨⟨⟨hX0, hXle⟩, hX1⟩, hsq0⟩, hsq1⟩, hcen⟩ := hok
        have h809 := mem_rat (p := 809) (q := 500) (by norm_num) (809 / 500) (by norm_num)
        have hX01 : ∀ v, mem X v → 0 < v ∧ v < 1 := fun v hv =>
          ⟨pos_of_lo_pos hv hX0, by linarith [pos_of_lo_pos (mem_sub mem_ONE hv) hX1]⟩
        exact centered1DPos_sound
          (f := fun v => h (v ^ 2) - (809 / 500 : ℝ) * v * h v)
          (f' := fun v => 2 * (v * hp (v ^ 2)) - (809 / 500 : ℝ) * (h v + v * hp v))
          hXle
          (fun I hlo hhi v hv => by
            have hv01 := hX01 v ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hv.1,
              le_trans hv.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩
            have hsq_mem := mem_clamp01 (mem_sq hv) (sq_nonneg v) (by nlinarith)
            have hres := mem_sub (mem_hIv hsq_mem (sq_nonneg v) (by nlinarith))
              (mem_mul h809 (mem_mul hv (mem_hIv hv (le_of_lt hv01.1) (le_of_lt hv01.2))))
            unfold bopp1DIv
            convert hres using 1; ring)
          (fun v hv => by
            have hv01 := hX01 v hv
            have hres := mem_sub (mem_mul (mem_ofInt 2) (mem_mul hv (mem_hpIv (mem_sq hv) hsq0 hsq1)))
              (mem_mul h809 (mem_add (mem_hIv hv (le_of_lt hv01.1) (le_of_lt hv01.2))
                (mem_mul hv (mem_hpIv hv hX0 hX1))))
            unfold bopp1DPIv; simpa using hres)
          (fun v hv => by
            have hv01 := hX01 v ⟨hv.1, hv.2⟩
            have hd1 : HasDerivAt (fun t => h (t ^ 2)) (hp (v ^ 2) * (2 * v)) v := by
              have hcomp : HasDerivAt (h ∘ fun t => t ^ 2) (hp (v ^ 2) * (2 * v ^ (2 - 1))) v :=
                HasDerivAt.comp (h := fun t => t ^ 2) v (hasDerivAt_h (sq_pos_of_pos hv01.1) (by nlinarith)) (hasDerivAt_pow 2 v)
              exact hcomp.congr_deriv (by ring)
            have hd2 : HasDerivAt (fun t => (809 / 500 : ℝ) * t * h t) ((809 / 500) * (h v + v * hp v)) v := by
              have := ((hasDerivAt_id' v).const_mul (809 / 500 : ℝ)).fun_mul (hasDerivAt_h hv01.1 hv01.2)
              exact this.congr_deriv (by ring)
            exact (hd1.fun_sub hd2).continuousAt.continuousWithinAt)
          (fun v hv => by
            have hv01 := hX01 v ⟨le_of_lt hv.1, le_of_lt hv.2⟩
            have hd1 : HasDerivAt (fun t => h (t ^ 2)) (hp (v ^ 2) * (2 * v)) v := by
              have hcomp : HasDerivAt (h ∘ fun t => t ^ 2) (hp (v ^ 2) * (2 * v ^ (2 - 1))) v :=
                HasDerivAt.comp (h := fun t => t ^ 2) v (hasDerivAt_h (sq_pos_of_pos hv01.1) (by nlinarith)) (hasDerivAt_pow 2 v)
              exact hcomp.congr_deriv (by ring)
            have hd2 : HasDerivAt (fun t => (809 / 500 : ℝ) * t * h t) ((809 / 500) * (h v + v * hp v)) v := by
              have := ((hasDerivAt_id' v).const_mul (809 / 500 : ℝ)).fun_mul (hasDerivAt_h hv01.1 hv01.2)
              exact this.congr_deriv (by ring)
            exact (hd1.fun_sub hd2).congr_deriv (by ring))
          hcen hu) chk_Bopp1D ⟨le_of_lt h1, h2⟩
      linarith
    · -- Analytic right strip s ∈ [1 - 1/4096, 1):
      push Not at h2
      set a := 1 - s
      have ha0 : 0 < a := by linarith
      have ha1 : a ≤ 1 / 4096 := by
        have hc : (c4096 : ℝ) / SCALE = 1 - 1 / 4096 := by unfold c4096 SCALE; norm_num
        linarith
      have hlog_ge : 12 * L ≤ -Real.log a := by
        have h1' : Real.log a ≤ Real.log (1 / 4096) := Real.log_le_log ha0 ha1
        have h12 : Real.log (1 / 4096 : ℝ) = -(12 * L) := by
          unfold L
          have : (1 / 4096 : ℝ) = (2 : ℝ) ^ (-12 : ℤ) := by norm_num
          rw [this, Real.log_zpow]; push_cast; ring
        linarith
      have hL1 : (1999 / 1000 : ℝ) * a * (-Real.log a - L) ≤ h (s ^ 2) := by
        rw [← h_symm (s ^ 2)]
        have h1ms2 : 1 - s ^ 2 = a * (2 - a) := by simp only [a]; ring
        rw [h1ms2]
        have hge := neg_mul_log_le_h (by nlinarith : (0 : ℝ) ≤ a * (2 - a)) (by nlinarith)
        have hlog_ub : Real.log (a * (2 - a)) ≤ Real.log (2 * a) :=
          Real.log_le_log (by nlinarith) (by nlinarith)
        rw [Real.log_mul (by norm_num) (ne_of_gt ha0)] at hlog_ub
        have hL_eq : Real.log 2 = L := rfl
        rw [hL_eq] at hlog_ub
        have hneg_ge : -Real.log a - L ≤ -Real.log (a * (2 - a)) := by linarith
        have hpos_neg : 0 ≤ -Real.log a - L := by linarith [L_pos]
        have hmul1 : (1999 / 1000 : ℝ) * a ≤ a * (2 - a) := by nlinarith
        have hmul2 : (1999 / 1000 : ℝ) * a * (-Real.log a - L) ≤ a * (2 - a) * (-Real.log (a * (2 - a))) :=
          mul_le_mul hmul1 hneg_ge hpos_neg (by nlinarith)
        linarith
      have hR1 : h s ≤ a * (1 - Real.log a) := by
        rw [← h_symm s]; exact h_le_mul_one_sub_log (by linarith)
      have hR2 : (809 / 500 : ℝ) * s * h s ≤ (809 / 500 : ℝ) * a * (1 - Real.log a) := by
        have := h_nonneg (le_of_lt hs_pos) (le_of_lt hs_lt)
        nlinarith
      nlinarith [const_L_gt]

end UCBound.Cert
