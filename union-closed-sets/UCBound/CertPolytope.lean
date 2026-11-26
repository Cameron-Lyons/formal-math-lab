module

public import UCBound.CertConst
public import UCBound.CertPolytopeTrees

@[expose] public section

/-!
# Certified 2D Polytope Positivity (`PhiG > 0` at 3 Vertices and `PhiT > 0` on `(0, z]`)

Witness-carrying 50-bit scaled-integer trees checked by Lean's kernel `decide` (zero `log` calls,
zero `native_decide`, zero `sorry`). Each leaf uses only Option A (exact `U`) or Option B
(Boppana `U`) with `(θ₁, θₛ)` weights—no `J_b`, no `F_pos`, no `Cut1`, no `Line2`, no Option C.
-/

namespace UCBound.Cert

open UCBound UCBound.Iv

/-! ### Precomputed Literal Constant Intervals for O(1) Kernel Lookup -/

def epsIv : Interval := ⟨410953465997, 410953465998⟩
def zIv : Interval := ⟨472877960873902, 472877960873903⟩
def cTotIv : Interval := ⟨1711367858400788, 1711367858400789⟩
def muUIv : Interval := ⟨3715469692580659, 3715469692580660⟩
def muGIv : Interval := ⟨30399297484750848, 30399297484750848⟩
def nu1Iv : Interval := ⟨217636451992679, 217636451992680⟩
def nu2Iv : Interval := ⟨-27021597764223, -27021597764222⟩
def boppCIv : Interval := ⟨1821706049271365, 1821706049271366⟩
def kF2Iv : Interval := ⟨123848989752688, 123848989752689⟩
def kE2Iv : Interval := ⟨472877960873902, 472877960873903⟩
def kSimRIv : Interval := ⟨67553994410557, 67553994410558⟩
def kSimVIv : Interval := ⟨292733975779082, 292733975779083⟩
def wSqHIv : Interval := ⟨-67553994410558, -67553994410557⟩
def wSqPhIv : Interval := ⟨771241436187197, 771241436187198⟩
def wSqRIv : Interval := ⟨303992974847508, 303992974847509⟩
def r4_5Iv : Interval := ⟨900719925474099, 900719925474100⟩
def r27_400Iv : Interval := ⟨75998243711877, 75998243711878⟩
def qLIv : Interval := ⟨182796046504768, 182796046504801⟩
def mSubEpsIv : Interval := ⟨694398474848583, 694398474848607⟩
def muUGIv : Interval := ⟨34114767177331507, 34114767177331508⟩

private lemma mem_epsIv : mem epsIv epsParam := by
  rw [show epsIv = ofRat 365 1000000 by decide]; unfold epsParam; convert mem_ofRat (p := 365) (q := 1000000) (by norm_num)
private lemma mem_zIv : mem zIv zParam := by
  rw [show zIv = ofRat 21 50 by decide]; unfold zParam; convert mem_ofRat (p := 21) (q := 50) (by norm_num)
private lemma mem_cTotIv : mem cTotIv CtotParam := by
  rw [show cTotIv = ofRat 152 100 by decide]; unfold CtotParam CcovParam; convert mem_ofRat (p := 152) (q := 100) (by norm_num); norm_num
private lemma mem_muUIv : mem muUIv muUParam := by
  rw [show muUIv = ofRat 33 10 by decide]; unfold muUParam; convert mem_ofRat (p := 33) (q := 10) (by norm_num)
private lemma mem_muGIv : mem muGIv mugParam := by
  rw [show muGIv = ofInt 27 by decide]; unfold mugParam; convert mem_ofInt 27
private lemma mem_nu1Iv : mem nu1Iv nu1Param := by
  rw [show nu1Iv = ofRat 1933 10000 by decide]; unfold nu1Param; convert mem_ofRat (p := 1933) (q := 10000) (by norm_num)
private lemma mem_nu2Iv : mem nu2Iv nu2Param := by
  rw [show nu2Iv = ofRat (-3) 125 by decide]; unfold nu2Param; convert mem_ofRat (p := -3) (q := 125) (by norm_num); norm_num
private lemma mem_boppCIv : mem boppCIv (809 / 500 : ℝ) := by
  rw [show boppCIv = ofRat 809 500 by decide]; convert mem_ofRat (p := 809) (q := 500) (by norm_num)
private lemma mem_kF2Iv : mem kF2Iv (11 / 100 : ℝ) := by
  rw [show kF2Iv = ofRat 11 100 by decide]; convert mem_ofRat (p := 11) (q := 100) (by norm_num)
private lemma mem_kE2Iv : mem kE2Iv (42 / 100 : ℝ) := by
  rw [show kE2Iv = ofRat 42 100 by decide]; convert mem_ofRat (p := 42) (q := 100) (by norm_num)
private lemma mem_kSimRIv : mem kSimRIv (6 / 100 : ℝ) := by
  rw [show kSimRIv = ofRat 6 100 by decide]; convert mem_ofRat (p := 6) (q := 100) (by norm_num)
private lemma mem_kSimVIv : mem kSimVIv (26 / 100 : ℝ) := by
  rw [show kSimVIv = ofRat 26 100 by decide]; convert mem_ofRat (p := 26) (q := 100) (by norm_num)
private lemma mem_wSqHIv : mem wSqHIv (-(3 / 50) : ℝ) := by
  rw [show wSqHIv = ofRat (-3) 50 by decide]; convert mem_ofRat (p := -3) (q := 50) (by norm_num); norm_num
private lemma mem_wSqPhIv : mem wSqPhIv (685 / 1000 : ℝ) := by
  rw [show wSqPhIv = ofRat 685 1000 by decide]; convert mem_ofRat (p := 685) (q := 1000) (by norm_num)
private lemma mem_wSqRIv : mem wSqRIv (27 / 100 : ℝ) := by
  rw [show wSqRIv = ofRat 27 100 by decide]; convert mem_ofRat (p := 27) (q := 100) (by norm_num)
private lemma mem_r4_5Iv : mem r4_5Iv (4 / 5 : ℝ) := by
  rw [show r4_5Iv = ofRat 4 5 by decide]; convert mem_ofRat (p := 4) (q := 5) (by norm_num)
private lemma mem_r27_400Iv : mem r27_400Iv (27 / 400 : ℝ) := by
  rw [show r27_400Iv = ofRat 27 400 by decide]; convert mem_ofRat (p := 27) (q := 400) (by norm_num)
private lemma mem_qLIv : mem qLIv (qStar * L) := by
  rw [show qLIv = mul constIv.q LN2 by decide]; exact mem_mul validConstIv.hq_mem mem_LN2
private lemma mem_mSubEpsIv : mem mSubEpsIv (mStar - epsParam) := by
  rw [show mSubEpsIv = sub constIv.m epsIv by decide]; exact mem_sub validConstIv.hm_mem mem_epsIv
private lemma mem_muUGIv : mem muUGIv (muUParam + mugParam) := by
  rw [show muUGIv = add muUIv muGIv by decide]; exact mem_add mem_muUIv mem_muGIv
private lemma constIv_p_neg : constIv.p.hi < 0 := by decide

/-! ### Precomputed Vertex Parameters for `G1`, `G2`, `G3` -/

structure GParams where
  ce_base : Interval
  ct_base : Interval
  cR_neg : Interval
  const_base : Interval

def computeGParams (wv_num omv_num : ℤ) (omv_den : ℕ) : GParams :=
  let wv := ofInt wv_num
  let omv := ofRat omv_num omv_den
  { ce_base := sub (sub (mul wv (divNeg constIv.bm constIv.p)) (mul constIv.D constIv.eta))
      (mul constIv.W omv)
    ct_base := mul wv (mul constIv.bm constIv.c)
    cR_neg := mul wv cTotIv
    const_base := sub (sub (mul constIv.W (mul omv constIv.eStar))
      (mul nu1Iv (sub wv constIv.eta))) (mul nu2Iv omv) }

/-! ### Infeasibility Pruning -/

def isInfeasible (E T : Interval) : Bool :=
  decide (E.lo > (add (mul r4_5Iv T) r27_400Iv).hi) ||
  decide ((sub (sub mSubEpsIv (divNeg E constIv.p)) (mul constIv.c T)).lo > (SCALE : ℤ)) ||
  decide ((add (divNeg E constIv.p) (mul constIv.c T)).lo > (SCALE : ℤ))

lemma isInfeasible_sound {E T : Interval} (hinf : isInfeasible E T = true)
    {s e t Rbar Fbar U_val g_val sq_val : ℝ}
    (vp : ValidPoint s e t Rbar Fbar U_val g_val sq_val)
    (he : mem E e) (ht : mem T t) : False := by
  unfold isInfeasible at hinf
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hinf
  have hS := SCALE_pos
  rcases hinf with (h1 | h2) | h3
  · have hmem := mem_add (mem_mul mem_r4_5Iv ht) mem_r27_400Iv
    linarith [lt_of_hi_lt_lo hmem he h1, vp.hline1]
  · have hmem := mem_sub (mem_sub mem_mSubEpsIv (mem_divNeg he validConstIv.hp_mem constIv_p_neg))
      (mem_mul validConstIv.hc_mem ht)
    have hgt : (1 : ℝ) < (mStar - epsParam) - e / pStar - cParam * t := by
      have h1 : (1 : ℝ) < ((sub (sub mSubEpsIv (divNeg E constIv.p)) (mul constIv.c T)).lo : ℝ) / SCALE := by
        rw [lt_div_iff₀ hS, one_mul]; exact_mod_cast h2
      linarith [hmem.1]
    linarith [vp.hs_lo, vp.hB_hi]
  · have hmem := mem_add (mem_divNeg he validConstIv.hp_mem constIv_p_neg) (mem_mul validConstIv.hc_mem ht)
    have hgt : (1 : ℝ) < e / pStar + cParam * t := by
      have h1 : (1 : ℝ) < ((add (divNeg E constIv.p) (mul constIv.c T)).lo : ℝ) / SCALE := by
        rw [lt_div_iff₀ hS, one_mul]; exact_mod_cast h3
      linarith [hmem.1]
    linarith [vp.hs_hi, vp.hB_lo]

/-! ### Single-Witness `R`-Elimination -/

def evalRElim (M1 cR_neg : Interval) (F_base_lo v2_lo tl th th1_i ths_i : ℤ) : ℤ :=
  let rem_i : ℤ := (SCALE : ℤ) - th1_i - ths_i
  let cp := mul M1 (add (mul (pt rem_i) (pt F_base_lo))
      (mul (pt ths_i) (mul kSimVIv (mul (pt tl) (pt v2_lo)))))
  let sr := sub (mul M1 (add (mul (pt th1_i) (mul kF2Iv (pt tl)))
      (mul (pt ths_i) (mul kSimRIv (pt tl))))) cR_neg
  if 0 ≤ sr.lo then cp.lo
  else (add cp (mul (pt sr.lo) (pt th))).lo

lemma evalRElim_sound {M1 cR_neg : Interval} {F_base_lo v2_lo tl th th1_i ths_i : ℤ}
    {M1_r cR_r s e t Rbar Fbar U_val g_val sq_val : ℝ}
    (vp : ValidPoint s e t Rbar Fbar U_val g_val sq_val)
    (hM1 : mem M1 M1_r) (hM1_nn : 0 ≤ M1_r) (hcR : mem cR_neg cR_r)
    (hFbase : (F_base_lo : ℝ) / SCALE ≤ Fbar)
    (hv2 : (v2_lo : ℝ) / SCALE ≤ (e - hr * t) ^ 2)
    (htl0 : 0 ≤ tl) (htl : (tl : ℝ) / SCALE ≤ t) (hth : t ≤ (th : ℝ) / SCALE)
    (hth1 : 0 ≤ th1_i) (hths : 0 ≤ ths_i) (hsum : th1_i + ths_i ≤ (SCALE : ℤ)) :
    (evalRElim M1 cR_neg F_base_lo v2_lo tl th th1_i ths_i : ℝ) / SCALE
      ≤ M1_r * Fbar - cR_r * Rbar := by
  have hS := SCALE_pos
  set rem_i : ℤ := (SCALE : ℤ) - th1_i - ths_i
  set θ1 : ℝ := (th1_i : ℝ) / SCALE
  set θs : ℝ := (ths_i : ℝ) / SCALE
  set rem : ℝ := (rem_i : ℝ) / SCALE
  set tl_r : ℝ := (tl : ℝ) / SCALE
  set Fb_r : ℝ := (F_base_lo : ℝ) / SCALE
  set v2_r : ℝ := (v2_lo : ℝ) / SCALE
  have hθ1_nn : 0 ≤ θ1 := div_nonneg (by exact_mod_cast hth1) (le_of_lt hS)
  have hθs_nn : 0 ≤ θs := div_nonneg (by exact_mod_cast hths) (le_of_lt hS)
  have hrem_nn : 0 ≤ rem := div_nonneg (by exact_mod_cast (show 0 ≤ rem_i by omega)) (le_of_lt hS)
  have htl_nn : 0 ≤ tl_r := div_nonneg (by exact_mod_cast htl0) (le_of_lt hS)
  have hpart : rem + θ1 + θs = 1 := by
    simp only [rem, θ1, θs, rem_i]; push_cast
    rw [sub_div, sub_div, div_self SCALE_ne_zero]; ring
  have hF1 : (11 / 100 : ℝ) * tl_r * Rbar ≤ Fbar := by
    have h1 : (11 / 100 : ℝ) * tl_r * Rbar ≤ 2 * (11 / 200 : ℝ) * t * Rbar :=
      mul_le_mul_of_nonneg_right (by linarith) vp.hR_lo
    linarith [vp.hF_R]
  have hFs : (6 / 100 : ℝ) * tl_r * Rbar + (26 / 100 : ℝ) * tl_r * v2_r ≤ Fbar := by
    have h1 : (6 / 100 : ℝ) * tl_r * Rbar ≤ 2 * (3 / 100 : ℝ) * t * Rbar :=
      mul_le_mul_of_nonneg_right (by linarith) vp.hR_lo
    have h2 : (26 / 100 : ℝ) * tl_r * v2_r ≤ 2 * (13 / 100 : ℝ) * t * (e - hr * t) ^ 2 := by
      calc (26 / 100 : ℝ) * tl_r * v2_r
          ≤ (26 / 100 : ℝ) * tl_r * (e - hr * t) ^ 2 := mul_le_mul_of_nonneg_left hv2 (by positivity)
        _ ≤ 2 * (13 / 100 : ℝ) * t * (e - hr * t) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith [vp.hF_sim]
  have hF_comb : rem * Fb_r + θs * ((26 / 100 : ℝ) * (tl_r * v2_r))
      + (θ1 * ((11 / 100 : ℝ) * tl_r) + θs * ((6 / 100 : ℝ) * tl_r)) * Rbar ≤ Fbar := by
    have hEq : Fbar = rem * Fbar + θ1 * Fbar + θs * Fbar := by
      calc Fbar = (rem + θ1 + θs) * Fbar := by rw [hpart, one_mul]
        _ = _ := by ring
    linarith [mul_le_mul_of_nonneg_left hFbase hrem_nn,
      mul_le_mul_of_nonneg_left hF1 hθ1_nn, mul_le_mul_of_nonneg_left hFs hθs_nn]
  set cp_r : ℝ := M1_r * (rem * Fb_r + θs * ((26 / 100 : ℝ) * (tl_r * v2_r)))
  set sr_r : ℝ := M1_r * (θ1 * ((11 / 100 : ℝ) * tl_r) + θs * ((6 / 100 : ℝ) * tl_r)) - cR_r
  have hmain : cp_r + sr_r * Rbar ≤ M1_r * Fbar - cR_r * Rbar := by
    have h1 := mul_le_mul_of_nonneg_left hF_comb hM1_nn
    have hEq : cp_r + sr_r * Rbar
        = M1_r * (rem * Fb_r + θs * ((26 / 100 : ℝ) * (tl_r * v2_r))
            + (θ1 * ((11 / 100 : ℝ) * tl_r) + θs * ((6 / 100 : ℝ) * tl_r)) * Rbar) - cR_r * Rbar := by
      simp only [cp_r, sr_r]; ring
    linarith
  set cp := mul M1 (add (mul (pt rem_i) (pt F_base_lo))
      (mul (pt ths_i) (mul kSimVIv (mul (pt tl) (pt v2_lo)))))
  set sr := sub (mul M1 (add (mul (pt th1_i) (mul kF2Iv (pt tl)))
      (mul (pt ths_i) (mul kSimRIv (pt tl))))) cR_neg
  have hcp_mem : mem cp cp_r :=
    mem_mul hM1 (mem_add (mem_mul (mem_pt rem_i) (mem_pt F_base_lo))
      (mem_mul (mem_pt ths_i) (mem_mul mem_kSimVIv (mem_mul (mem_pt tl) (mem_pt v2_lo)))))
  have hsr_mem : mem sr sr_r :=
    mem_sub (mem_mul hM1 (mem_add (mem_mul (mem_pt th1_i) (mem_mul mem_kF2Iv (mem_pt tl)))
      (mem_mul (mem_pt ths_i) (mem_mul mem_kSimRIv (mem_pt tl))))) hcR
  unfold evalRElim; dsimp only
  change ((if 0 ≤ sr.lo then cp.lo else (add cp (mul (pt sr.lo) (pt th))).lo : ℤ) : ℝ) / SCALE ≤ _
  split_ifs with hsr0
  · have hsr_nn : 0 ≤ sr_r := le_trans (div_nonneg (by exact_mod_cast hsr0) (le_of_lt hS)) hsr_mem.1
    linarith [mul_nonneg hsr_nn vp.hR_lo, hcp_mem.1]
  · push Not at hsr0
    have hadd := mem_add hcp_mem (mem_mul (mem_pt sr.lo) (mem_pt th))
    have hsr_neg : (sr.lo : ℝ) / SCALE ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (le_of_lt hsr0)) (le_of_lt hS)
    have hRhi : Rbar ≤ (th : ℝ) / SCALE := le_trans vp.hR_le_t hth
    have hsr_le : (sr.lo : ℝ) / SCALE * ((th : ℝ) / SCALE) ≤ sr_r * Rbar :=
      le_trans (mul_le_mul_of_nonpos_left hRhi hsr_neg) (mul_le_mul_of_nonneg_right hsr_mem.1 vp.hR_lo)
    linarith [hadd.1]

/-! ### Common Box Bounds -/

structure CommonBounds where
  s_lo : Interval
  v2_lo : ℤ
  F_base_lo : ℤ

def commonBoxBounds (E T : Interval) : CommonBounds :=
  let s_lo := pt (maxIv mSubEpsIv (add (divNeg E constIv.p) (mul constIv.c T))).lo
  let v2_lo := (sq (sub E (mul constIv.hr T))).lo
  let F_base_lo := max 0 (mul kE2Iv (mul (pt T.lo) (pt v2_lo))).lo
  { s_lo := s_lo, v2_lo := v2_lo, F_base_lo := F_base_lo }

lemma commonBoxBounds_sound {E T : Interval} (hT0 : 0 ≤ T.lo)
    {s e t Rbar Fbar U_val g_val sq_val : ℝ}
    (vp : ValidPoint s e t Rbar Fbar U_val g_val sq_val)
    (he : mem E e) (ht : mem T t) :
    let cb := commonBoxBounds E T
    (cb.s_lo.lo : ℝ) / SCALE ≤ s ∧
    (cb.v2_lo : ℝ) / SCALE ≤ (e - hr * t) ^ 2 ∧
    (cb.F_base_lo : ℝ) / SCALE ≤ Fbar := by
  have hS := SCALE_pos
  have hT_nn : (0 : ℝ) ≤ (T.lo : ℝ) / SCALE := div_nonneg (by exact_mod_cast hT0) (le_of_lt hS)
  set cb := commonBoxBounds E T
  have hs_lo : (cb.s_lo.lo : ℝ) / SCALE ≤ s := by
    have hmax := mem_maxIv mem_mSubEpsIv
      (mem_add (mem_divNeg he validConstIv.hp_mem constIv_p_neg) (mem_mul validConstIv.hc_mem ht))
    exact le_trans hmax.1 (max_le vp.hs_lo (by linarith [vp.hB_lo]))
  have hv2_lo : (cb.v2_lo : ℝ) / SCALE ≤ (e - hr * t) ^ 2 :=
    (mem_sq (mem_sub he (mem_mul validConstIv.hhr_mem ht))).1
  have hF_base_lo : (cb.F_base_lo : ℝ) / SCALE ≤ Fbar := by
    have hFv_mem := mem_mul mem_kE2Iv (mem_mul (mem_pt T.lo) (mem_pt cb.v2_lo))
    have hFv_le : ((mul kE2Iv (mul (pt T.lo) (pt cb.v2_lo))).lo : ℝ) / SCALE ≤ Fbar := by
      have hstep1 := mul_le_mul_of_nonneg_left hv2_lo hT_nn
      have hstep2 := mul_le_mul_of_nonneg_right ht.1 (sq_nonneg (e - hr * t))
      linarith [hFv_mem.1, vp.hF_v]
    dsimp only [cb, commonBoxBounds]
    rw [Int.cast_max, max_div_pos (le_of_lt hS), Int.cast_zero, zero_div]
    exact max_le vp.hF_lo hFv_le
  exact ⟨hs_lo, hv2_lo, hF_base_lo⟩

/-! ### Concave Quadratic Minimum Helper -/

private lemma concave_quad_min {a b tl th t : ℝ} (hb : 0 ≤ b) (h1 : tl ≤ t) (h2 : t ≤ th) :
    min (a * tl - b * tl ^ 2) (a * th - b * th ^ 2) ≤ a * t - b * t ^ 2 := by
  have hprod : 0 ≤ (t - tl) * (th - t) := mul_nonneg (by linarith) (by linarith)
  by_cases htlh : tl = th
  · subst htlh; have : t = tl := le_antisymm h2 h1; subst this; simp
  · have hpos : 0 < th - tl := lt_of_le_of_ne (by linarith) (fun h => htlh (by linarith))
    set u := (t - tl) / (th - tl)
    have hu0 : 0 ≤ u := div_nonneg (by linarith) (le_of_lt hpos)
    have hu1 : u ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have hlin : (1 - u) * (a * tl - b * tl ^ 2) + u * (a * th - b * th ^ 2)
        = a * t - b * t ^ 2 - b * ((t - tl) * (th - t)) := by
      have ht_eq : t = (1 - u) * tl + u * th := by simp only [u]; field_simp [ne_of_gt hpos]; ring
      rw [ht_eq]
      have : ((1 - u) * tl + u * th - tl) * (th - ((1 - u) * tl + u * th))
          = u * (1 - u) * (th - tl) ^ 2 := by ring
      rw [this]; ring
    have ha := min_le_left (a * tl - b * tl ^ 2) (a * th - b * th ^ 2)
    have hb' := min_le_right (a * tl - b * tl ^ 2) (a * th - b * th ^ 2)
    have hbn : 0 ≤ b * ((t - tl) * (th - t)) := mul_nonneg hb hprod
    nlinarith

/-! ### Witness-Driven Leaf Checkers for `G` and `T` (Options A & B Only) -/

def checkTheta (th1 ths : ℤ) : Bool :=
  decide (0 ≤ th1) && decide (0 ≤ ths) && decide (th1 + ths ≤ (SCALE : ℤ))

def leafOkG (gp : GParams) (E T : Interval) : GWit → Bool
  | .infeas => isInfeasible E T
  | .optA th1 ths =>
    checkTheta th1 ths &&
    match commonBoxBounds E T with
    | ⟨s_lo, v2_lo, F_base_lo⟩ =>
      let ce_A := add (add gp.ce_base (mul muUIv (sub (mul (ofInt 2) s_lo) ONE)))
        (mul (ofInt 2) (mul muGIv (sub s_lo constIv.m)))
      let tA_l := (sub (mul gp.ct_base (pt T.lo)) (mul muUIv (mul qLIv (sq (pt T.lo))))).lo
      let tA_h := (sub (mul gp.ct_base (pt T.hi)) (mul muUIv (mul qLIv (sq (pt T.hi))))).lo
      let rA := evalRElim muUGIv gp.cR_neg F_base_lo v2_lo T.lo T.hi th1 ths
      decide (0 < gp.const_base.lo + (mul ce_A E).lo + min tA_l tA_h + rA)
  | .optB th1 ths =>
    checkTheta th1 ths &&
    match commonBoxBounds E T with
    | ⟨s_lo, v2_lo, F_base_lo⟩ =>
      let ce_B := add (add gp.ce_base (mul muUIv (sub (mul boppCIv s_lo) ONE)))
        (mul (ofInt 2) (mul muGIv (sub s_lo constIv.m)))
      let rB := evalRElim muGIv gp.cR_neg F_base_lo v2_lo T.lo T.hi th1 ths
      decide (0 < gp.const_base.lo + (mul ce_B E).lo + (mul gp.ct_base (pt T.lo)).lo + rB)

def leafOkT (E T : Interval) : TWit → Bool
  | .infeas => isInfeasible E T
  | .optA a_i th1 ths =>
    decide (0 ≤ a_i) && checkTheta th1 ths &&
    match commonBoxBounds E T with
    | ⟨s_lo, v2_lo, F_base_lo⟩ =>
      let S0_lo := (add (mul wSqHIv E) (mul wSqPhIv T)).lo
      let sq_const := (sub (mul (ofInt 2) (mul (pt a_i) (pt S0_lo))) (sq (pt a_i))).lo
      let cR_neg := mul (ofInt 2) (mul (pt a_i) wSqRIv)
      let ce_A := add (add (neg constIv.m) (mul muUIv (sub (mul (ofInt 2) s_lo) ONE)))
        (mul (ofInt 2) (mul muGIv (sub s_lo constIv.m)))
      let rA := evalRElim muUGIv cR_neg F_base_lo v2_lo T.lo T.hi th1 ths
      decide (0 < sq_const + (mul ce_A E).lo - (mul muUIv (mul qLIv (sq (pt T.hi)))).hi + rA)
  | .optB a_i th1 ths =>
    decide (0 ≤ a_i) && checkTheta th1 ths &&
    match commonBoxBounds E T with
    | ⟨s_lo, v2_lo, F_base_lo⟩ =>
      let S0_lo := (add (mul wSqHIv E) (mul wSqPhIv T)).lo
      let sq_const := (sub (mul (ofInt 2) (mul (pt a_i) (pt S0_lo))) (sq (pt a_i))).lo
      let cR_neg := mul (ofInt 2) (mul (pt a_i) wSqRIv)
      let ce_B := add (add (neg constIv.m) (mul muUIv (sub (mul boppCIv s_lo) ONE)))
        (mul (ofInt 2) (mul muGIv (sub s_lo constIv.m)))
      let rB := evalRElim muGIv cR_neg F_base_lo v2_lo T.lo T.hi th1 ths
      decide (0 < sq_const + (mul ce_B E).lo + rB)

lemma leafOkG_sound {wv_num omv_num : ℤ} {omv_den : ℕ} (hden : 0 < omv_den) (hwv0 : 0 ≤ wv_num)
    {gp : GParams} (hgp : gp = computeGParams wv_num omv_num omv_den)
    {E T : Interval} (hT0 : 0 ≤ T.lo) {w : GWit} (hok : leafOkG gp E T w = true)
    {s e t Rbar Fbar U_val g_val sq_val : ℝ}
    (vp : ValidPoint s e t Rbar Fbar U_val g_val sq_val)
    (he : mem E e) (ht : mem T t) :
    0 < PhiG (wv_num : ℝ) ((omv_num : ℝ) / (omv_den : ℝ)) s e t Rbar U_val g_val := by
  subst hgp
  have hS := SCALE_pos
  set wv_r : ℝ := (wv_num : ℝ)
  set omv_r : ℝ := (omv_num : ℝ) / (omv_den : ℝ)
  have hwv_mem : mem (ofInt wv_num) wv_r := mem_ofInt wv_num
  have homv_mem : mem (ofRat omv_num omv_den) omv_r := mem_ofRat (p := omv_num) (q := omv_den) hden
  have hwv_nn : 0 ≤ wv_r := by dsimp only [wv_r]; exact_mod_cast hwv0
  set gp := computeGParams wv_num omv_num omv_den
  set ce_base_r : ℝ := wv_r * (bm / pStar) - DParam * etaParam - WParam * omv_r
  set ct_base_r : ℝ := wv_r * (bm * cParam)
  set cR_neg_r : ℝ := wv_r * CtotParam
  set const_base_r : ℝ := WParam * (omv_r * eStar) - nu1Param * (wv_r - etaParam) - nu2Param * omv_r
  have hce_base : mem gp.ce_base ce_base_r :=
    mem_sub (mem_sub (mem_mul hwv_mem (mem_divNeg validConstIv.hbm_mem validConstIv.hp_mem constIv_p_neg))
      (mem_mul validConstIv.hD_mem validConstIv.heta_mem)) (mem_mul validConstIv.hW_mem homv_mem)
  have hct_base : mem gp.ct_base ct_base_r :=
    mem_mul hwv_mem (mem_mul validConstIv.hbm_mem validConstIv.hc_mem)
  have hcR_neg : mem gp.cR_neg cR_neg_r := mem_mul hwv_mem mem_cTotIv
  have hconst_base : mem gp.const_base const_base_r :=
    mem_sub (mem_sub (mem_mul validConstIv.hW_mem (mem_mul homv_mem validConstIv.heStar_mem))
      (mem_mul mem_nu1Iv (mem_sub hwv_mem validConstIv.heta_mem))) (mem_mul mem_nu2Iv homv_mem)
  have hct_nn : 0 ≤ ct_base_r := mul_nonneg hwv_nn
    (mul_nonneg (le_of_lt (pos_of_lo_pos validConstIv.hbm_mem (by decide)))
      (le_of_lt (pos_of_lo_pos validConstIv.hc_mem (by decide))))
  have hqL_pos : 0 < qStar * L := pos_of_lo_pos mem_qLIv (by decide)
  have hPhi_rew : PhiG wv_r omv_r s e t Rbar U_val g_val
      = const_base_r + ce_base_r * e + ct_base_r * t - cR_neg_r * Rbar
        + muUParam * (U_val - e) + mugParam * (g_val + 2 * (s - mStar) * e) := by
    unfold PhiG; simp only [const_base_r, ce_base_r, ct_base_r, cR_neg_r]; ring
  have hg_ge : mugParam * Fbar ≤ mugParam * g_val :=
    mul_le_mul_of_nonneg_left vp.hF_le_g mugParam_nonneg
  cases w with
  | infeas => exact False.elim (isInfeasible_sound hok vp he ht)
  | optA th1 ths =>
    unfold leafOkG checkTheta at hok; dsimp only at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hth1, hths⟩, hsum⟩, hval⟩ := hok
    obtain ⟨hs_lo, hv2_lo, hF_base_lo⟩ := commonBoxBounds_sound hT0 vp he ht
    set cb := commonBoxBounds E T
    set s_lo_r : ℝ := (cb.s_lo.lo : ℝ) / SCALE
    have hs_lo_mem : mem cb.s_lo s_lo_r := mem_pt cb.s_lo.lo
    set ce_A_r : ℝ := ce_base_r + muUParam * (2 * s_lo_r - 1) + 2 * (mugParam * (s_lo_r - mStar))
    have hceA_e := mem_mul (mem_add (mem_add hce_base
      (mem_mul mem_muUIv (mem_sub (mem_mul (mem_ofInt 2) hs_lo_mem) mem_ONE)))
      (mem_mul (mem_ofInt 2) (mem_mul mem_muGIv (mem_sub hs_lo_mem validConstIv.hm_mem)))) he
    have htAl := mem_sub (mem_mul hct_base (mem_pt T.lo)) (mem_mul mem_muUIv (mem_mul mem_qLIv (mem_sq (mem_pt T.lo))))
    have htAh := mem_sub (mem_mul hct_base (mem_pt T.hi)) (mem_mul mem_muUIv (mem_mul mem_qLIv (mem_sq (mem_pt T.hi))))
    have htA_le : ((min (sub (mul gp.ct_base (pt T.lo)) (mul muUIv (mul qLIv (sq (pt T.lo))))).lo
        (sub (mul gp.ct_base (pt T.hi)) (mul muUIv (mul qLIv (sq (pt T.hi))))).lo : ℤ) : ℝ) / SCALE
        ≤ ct_base_r * t - muUParam * (qStar * L) * t ^ 2 := by
      rw [Int.cast_min, min_div_pos (le_of_lt hS)]
      exact le_trans (min_le_min (by linarith [htAl.1]) (by linarith [htAh.1]))
        (concave_quad_min (mul_nonneg muUParam_nonneg (le_of_lt hqL_pos)) ht.1 ht.2)
    have hrA := evalRElim_sound vp mem_muUGIv (by linarith [muUParam_nonneg, mugParam_nonneg])
      hcR_neg hF_base_lo hv2_lo hT0 ht.1 ht.2 hth1 hths hsum
    have hpos : (0 : ℝ) < ((_ : ℤ) : ℝ) / SCALE := div_pos (by exact_mod_cast hval) hS
    rw [hPhi_rew, vp.hU_eq]
    have hs_inc : ce_A_r * e ≤ (ce_base_r + muUParam * (2 * s - 1) + 2 * (mugParam * (s - mStar))) * e := by
      apply mul_le_mul_of_nonneg_right _ vp.he_lo
      have := muUParam_nonneg; have := mugParam_nonneg; dsimp only [ce_A_r]; nlinarith
    push_cast at hpos hceA_e htA_le; simp only [add_div] at hpos
    have hceA_lo := hceA_e.1
    dsimp only [ce_A_r] at hs_inc
    linarith [hconst_base.1, hceA_lo, htA_le, hrA, hg_ge, hs_inc, hpos]
  | optB th1 ths =>
    unfold leafOkG checkTheta at hok; dsimp only at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hth1, hths⟩, hsum⟩, hval⟩ := hok
    obtain ⟨hs_lo, hv2_lo, hF_base_lo⟩ := commonBoxBounds_sound hT0 vp he ht
    set cb := commonBoxBounds E T
    set s_lo_r : ℝ := (cb.s_lo.lo : ℝ) / SCALE
    have hs_lo_mem : mem cb.s_lo s_lo_r := mem_pt cb.s_lo.lo
    set ce_B_r : ℝ := ce_base_r + muUParam * ((809 / 500 : ℝ) * s_lo_r - 1) + 2 * (mugParam * (s_lo_r - mStar))
    have hceB_e := mem_mul (mem_add (mem_add hce_base
      (mem_mul mem_muUIv (mem_sub (mem_mul mem_boppCIv hs_lo_mem) mem_ONE)))
      (mem_mul (mem_ofInt 2) (mem_mul mem_muGIv (mem_sub hs_lo_mem validConstIv.hm_mem)))) he
    have htB := mem_mul hct_base (mem_pt T.lo)
    have htB_le : ct_base_r * ((T.lo : ℝ) / SCALE) ≤ ct_base_r * t := mul_le_mul_of_nonneg_left ht.1 hct_nn
    have hrB := evalRElim_sound vp mem_muGIv mugParam_nonneg hcR_neg hF_base_lo hv2_lo
      hT0 ht.1 ht.2 hth1 hths hsum
    have hpos : (0 : ℝ) < ((_ : ℤ) : ℝ) / SCALE := div_pos (by exact_mod_cast hval) hS
    rw [hPhi_rew]
    have hU_ge := mul_le_mul_of_nonneg_left (show (809 / 500 : ℝ) * s * e - e ≤ U_val - e by linarith [vp.hU_bopp]) muUParam_nonneg
    have hs_inc : ce_B_r * e ≤ (ce_base_r + muUParam * ((809 / 500 : ℝ) * s - 1) + 2 * (mugParam * (s - mStar))) * e := by
      apply mul_le_mul_of_nonneg_right _ vp.he_lo
      have := muUParam_nonneg; have := mugParam_nonneg; dsimp only [ce_B_r]; nlinarith
    push_cast at hpos hceB_e; simp only [add_div] at hpos
    have hceB_lo := hceB_e.1
    dsimp only [ce_B_r] at hs_inc
    linarith [hconst_base.1, hceB_lo, htB.1, htB_le, hrB, hg_ge, hU_ge, hs_inc, hpos]

private lemma sq_tangent_lb {E T : Interval} {a_i : ℤ} (ha0 : 0 ≤ a_i)
    {s e t Rbar Fbar U_val g_val sq_val : ℝ}
    (vp : ValidPoint s e t Rbar Fbar U_val g_val sq_val) (he : mem E e) (ht : mem T t) :
    let S0_lo := (add (mul wSqHIv E) (mul wSqPhIv T)).lo
    let a_r : ℝ := (a_i : ℝ) / SCALE
    (2 * (a_r * ((S0_lo : ℝ) / SCALE)) - a_r ^ 2) - (2 * (a_r * (27 / 100 : ℝ))) * Rbar ≤ sq_val := by
  have ha_nn : 0 ≤ (a_i : ℝ) / SCALE := div_nonneg (by exact_mod_cast ha0) (le_of_lt SCALE_pos)
  have hS0_mem := mem_add (mem_mul mem_wSqHIv he) (mem_mul mem_wSqPhIv ht)
  set S0_lo := (add (mul wSqHIv E) (mul wSqPhIv T)).lo
  set a_r : ℝ := (a_i : ℝ) / SCALE
  set u := max 0 (-(3 / 50 : ℝ) * e + (685 / 1000 : ℝ) * t - (27 / 100 : ℝ) * Rbar)
  have hu_ge : (S0_lo : ℝ) / SCALE - (27 / 100 : ℝ) * Rbar ≤ u := le_trans (by linarith [hS0_mem.1]) (le_max_right _ _)
  have h1 : 2 * a_r * ((S0_lo : ℝ) / SCALE - (27 / 100 : ℝ) * Rbar) - a_r ^ 2 ≤ 2 * a_r * u - a_r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hu_ge (by linarith : 0 ≤ 2 * a_r); linarith
  have h2 : 2 * a_r * u - a_r ^ 2 ≤ u ^ 2 := by nlinarith [sq_nonneg (u - a_r)]
  have hEq : (2 * (a_r * ((S0_lo : ℝ) / SCALE)) - a_r ^ 2) - (2 * (a_r * (27 / 100 : ℝ))) * Rbar
      = 2 * a_r * ((S0_lo : ℝ) / SCALE - (27 / 100 : ℝ) * Rbar) - a_r ^ 2 := by ring
  have hu_sq : u ^ 2 ≤ sq_val := vp.hsq_lo
  linarith

lemma leafOkT_sound {E T : Interval} (hT0 : 0 ≤ T.lo) {w : TWit} (hok : leafOkT E T w = true)
    {s e t Rbar Fbar U_val g_val sq_val : ℝ}
    (vp : ValidPoint s e t Rbar Fbar U_val g_val sq_val)
    (he : mem E e) (ht : mem T t) :
    0 < PhiT s e t Rbar sq_val U_val g_val := by
  have hS := SCALE_pos
  have hqL_pos : 0 < qStar * L := pos_of_lo_pos mem_qLIv (by decide)
  have hg_ge : mugParam * Fbar ≤ mugParam * g_val :=
    mul_le_mul_of_nonneg_left vp.hF_le_g mugParam_nonneg
  cases w with
  | infeas => exact False.elim (isInfeasible_sound hok vp he ht)
  | optA a_i th1 ths =>
    unfold leafOkT checkTheta at hok; dsimp only at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨ha0, ⟨⟨hth1, hths⟩, hsum⟩⟩, hval⟩ := hok
    obtain ⟨hs_lo, hv2_lo, hF_base_lo⟩ := commonBoxBounds_sound hT0 vp he ht
    set cb := commonBoxBounds E T
    set s_lo_r : ℝ := (cb.s_lo.lo : ℝ) / SCALE
    have hs_lo_mem : mem cb.s_lo s_lo_r := mem_pt cb.s_lo.lo
    set S0_lo : ℤ := (add (mul wSqHIv E) (mul wSqPhIv T)).lo
    have hsq_tan := sq_tangent_lb ha0 vp he ht
    have hsq_c := mem_sub (mem_mul (mem_ofInt 2) (mem_mul (mem_pt a_i) (mem_pt S0_lo))) (mem_sq (mem_pt a_i))
    have hcR_neg := mem_mul (mem_ofInt 2) (mem_mul (mem_pt a_i) mem_wSqRIv)
    set ce_A_r : ℝ := -mStar + muUParam * (2 * s_lo_r - 1) + 2 * (mugParam * (s_lo_r - mStar))
    have hceA_e := mem_mul (mem_add (mem_add (mem_neg validConstIv.hm_mem)
      (mem_mul mem_muUIv (mem_sub (mem_mul (mem_ofInt 2) hs_lo_mem) mem_ONE)))
      (mem_mul (mem_ofInt 2) (mem_mul mem_muGIv (mem_sub hs_lo_mem validConstIv.hm_mem)))) he
    have hqt_hi := mem_mul mem_muUIv (mem_mul mem_qLIv (mem_sq (mem_pt T.hi)))
    have hqt_le : muUParam * (qStar * L * t ^ 2) ≤ muUParam * ((qStar * L) * ((T.hi : ℝ) / SCALE) ^ 2) := by
      have hsq_le : t ^ 2 ≤ ((T.hi : ℝ) / SCALE) ^ 2 := by nlinarith [vp.ht_lo, ht.2]
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq_le (le_of_lt hqL_pos)) muUParam_nonneg
      linarith
    have hrA := evalRElim_sound vp mem_muUGIv (by linarith [muUParam_nonneg, mugParam_nonneg])
      hcR_neg hF_base_lo hv2_lo hT0 ht.1 ht.2 hth1 hths hsum
    have hpos : (0 : ℝ) < ((_ : ℤ) : ℝ) / SCALE := div_pos (by exact_mod_cast hval) hS
    unfold PhiT; rw [vp.hU_eq]
    have hs_inc : ce_A_r * e ≤ (-mStar + muUParam * (2 * s - 1) + 2 * (mugParam * (s - mStar))) * e := by
      apply mul_le_mul_of_nonneg_right _ vp.he_lo
      have := muUParam_nonneg; have := mugParam_nonneg; dsimp only [ce_A_r]; nlinarith
    push_cast at hpos hceA_e hsq_c hrA; simp only [add_div, sub_div] at hpos
    have hceA_lo := hceA_e.1
    dsimp only [ce_A_r] at hs_inc
    linarith [hsq_tan, hsq_c.1, hceA_lo, hqt_hi.2, hqt_le, hrA, hg_ge, hs_inc, hpos]
  | optB a_i th1 ths =>
    unfold leafOkT checkTheta at hok; dsimp only at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨ha0, ⟨⟨hth1, hths⟩, hsum⟩⟩, hval⟩ := hok
    obtain ⟨hs_lo, hv2_lo, hF_base_lo⟩ := commonBoxBounds_sound hT0 vp he ht
    set cb := commonBoxBounds E T
    set s_lo_r : ℝ := (cb.s_lo.lo : ℝ) / SCALE
    have hs_lo_mem : mem cb.s_lo s_lo_r := mem_pt cb.s_lo.lo
    set S0_lo : ℤ := (add (mul wSqHIv E) (mul wSqPhIv T)).lo
    have hsq_tan := sq_tangent_lb ha0 vp he ht
    have hsq_c := mem_sub (mem_mul (mem_ofInt 2) (mem_mul (mem_pt a_i) (mem_pt S0_lo))) (mem_sq (mem_pt a_i))
    have hcR_neg := mem_mul (mem_ofInt 2) (mem_mul (mem_pt a_i) mem_wSqRIv)
    set ce_B_r : ℝ := -mStar + muUParam * ((809 / 500 : ℝ) * s_lo_r - 1) + 2 * (mugParam * (s_lo_r - mStar))
    have hceB_e := mem_mul (mem_add (mem_add (mem_neg validConstIv.hm_mem)
      (mem_mul mem_muUIv (mem_sub (mem_mul mem_boppCIv hs_lo_mem) mem_ONE)))
      (mem_mul (mem_ofInt 2) (mem_mul mem_muGIv (mem_sub hs_lo_mem validConstIv.hm_mem)))) he
    have hrB := evalRElim_sound vp mem_muGIv mugParam_nonneg hcR_neg hF_base_lo hv2_lo
      hT0 ht.1 ht.2 hth1 hths hsum
    have hpos : (0 : ℝ) < ((_ : ℤ) : ℝ) / SCALE := div_pos (by exact_mod_cast hval) hS
    unfold PhiT
    have hU_ge := mul_le_mul_of_nonneg_left (show (809 / 500 : ℝ) * s * e - e ≤ U_val - e by linarith [vp.hU_bopp]) muUParam_nonneg
    have hs_inc : ce_B_r * e ≤ (-mStar + muUParam * ((809 / 500 : ℝ) * s - 1) + 2 * (mugParam * (s - mStar))) * e := by
      apply mul_le_mul_of_nonneg_right _ vp.he_lo
      have := muUParam_nonneg; have := mugParam_nonneg; dsimp only [ce_B_r]; nlinarith
    push_cast at hpos hceB_e hsq_c hrB; simp only [add_div] at hpos
    have hceB_lo := hceB_e.1
    dsimp only [ce_B_r] at hs_inc
    linarith [hsq_tan, hsq_c.1, hceB_lo, hrB, hg_ge, hU_ge, hs_inc, hpos]

/-! ### Generic `PolyTree` Checker & Soundness -/

def checkPolyTree {W : Type} (pred : Interval → Interval → W → Bool)
    (xlo xhi ylo yhi : ℤ) : PolyTree W → Bool
  | .leaf w => pred ⟨xlo, xhi⟩ ⟨ylo, yhi⟩ w
  | .cutX m l r =>
    decide (xlo ≤ m) && decide (m ≤ xhi) &&
    checkPolyTree pred xlo m ylo yhi l && checkPolyTree pred m xhi ylo yhi r
  | .cutY m l r =>
    decide (ylo ≤ m) && decide (m ≤ yhi) &&
    checkPolyTree pred xlo xhi ylo m l && checkPolyTree pred xlo xhi m yhi r

private lemma checkPolyTree_sound_y0 {W : Type} {pred : Interval → Interval → W → Bool} {P : ℝ → ℝ → Prop}
    (hpred : ∀ Ix Iy w, 0 ≤ Iy.lo → pred Ix Iy w = true → ∀ x y, mem Ix x → mem Iy y → P x y)
    {xlo xhi ylo yhi : ℤ} (hy0 : 0 ≤ ylo) {t : PolyTree W}
    (hchk : checkPolyTree pred xlo xhi ylo yhi t = true)
    {x y : ℝ} (hx : mem ⟨xlo, xhi⟩ x) (hy : mem ⟨ylo, yhi⟩ y) : P x y := by
  induction t generalizing xlo xhi ylo yhi with
  | leaf w => exact hpred ⟨xlo, xhi⟩ ⟨ylo, yhi⟩ w hy0 hchk x y hx hy
  | cutX m l r ihl ihr =>
    unfold checkPolyTree at hchk; simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases le_total x ((m : ℝ) / SCALE) with hxm | hmx
    · exact ihl hy0 hchk.1.2 ⟨hx.1, hxm⟩ hy
    · exact ihr hy0 hchk.2 ⟨hmx, hx.2⟩ hy
  | cutY m l r ihl ihr =>
    unfold checkPolyTree at hchk; simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases le_total y ((m : ℝ) / SCALE) with hym | hmy
    · exact ihl hy0 hchk.1.2 hx ⟨hy.1, hym⟩
    · exact ihr (le_trans hy0 hchk.1.1.1) hchk.2 hx ⟨hmy, hy.2⟩

/-! ### Precomputed Literal `GParams` + Pure-Kernel `decide` Checks -/

def gp1 : GParams := computeGParams 0 3 8
def gp2 : GParams := computeGParams 1 3 8
def gp3 : GParams := computeGParams 1 (-5) 8

set_option maxHeartbeats 2000000 in
lemma check_treeG1 : checkPolyTree (leafOkG gp1) zLoCut LHiCut 0 (SCALE : ℤ) treeG1 = true := by decide

set_option maxHeartbeats 2000000 in
lemma check_treeG2 : checkPolyTree (leafOkG gp2) zLoCut LHiCut 0 (SCALE : ℤ) treeG2 = true := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma check_treeG3 : checkPolyTree (leafOkG gp3) zLoCut LHiCut 0 (SCALE : ℤ) treeG3 = true := by decide

set_option maxHeartbeats 2000000 in
lemma check_treeT : checkPolyTree leafOkT e1Cut zHiCut 0 (SCALE : ℤ) treeT = true := by decide

/-! ### Analytic Small-`e` Proof of `PhiT > 0` for `0 < e ≤ e1Cut / SCALE` -/

lemma PhiT_pos_small_e {s e t Rbar Fbar U_val g_val sq_val : ℝ}
    (vp : ValidPoint s e t Rbar Fbar U_val g_val sq_val)
    (he0 : 0 < e) (he1 : e ≤ (e1Cut : ℝ) / SCALE) :
    0 < PhiT s e t Rbar sq_val U_val g_val := by
  -- Step 1: Eliminate Rbar using hsq_lo + mugParam * hF_R, then separate t^2 and e^2 via (m - 39*B)^2 ≥ 0.
  have hsqF : (731991 / 1600000 : ℝ) * t ^ 2 - (351 / 2500 : ℝ) * e ^ 2 ≤ sq_val + mugParam * Fbar := by
    set u := (685 / 1000 : ℝ) * t - (3 / 50 : ℝ) * e
    set w := u - (27 / 100 : ℝ) * Rbar
    have hsq_nn : 0 ≤ sq_val := le_trans (sq_nonneg _) vp.hsq_lo
    have hF_R : (27 : ℝ) * ((11 / 100 : ℝ) * t * Rbar) ≤ mugParam * Fbar := by
      unfold mugParam; linarith [vp.hF_R]
    have hm_sq : (max 0 u) ^ 2 ≤ sq_val + mugParam * Fbar := by
      rcases le_or_gt u 0 with hu0 | hu0
      · rw [max_eq_left hu0]; nlinarith [vp.hF_lo, mugParam_nonneg]
      · rw [max_eq_right (le_of_lt hu0)]
        have hu_le : u ≤ (685 / 1000 : ℝ) * t := by dsimp only [u]; linarith [vp.he_lo]
        rcases le_or_gt 0 w with hw0 | hw0
        · have hw_sq : w ^ 2 ≤ sq_val := by
            have h1 := vp.hsq_lo
            have heq : -(3 / 50 : ℝ) * e + (685 / 1000 : ℝ) * t - (27 / 100 : ℝ) * Rbar = w := by dsimp only [w, u]; ring
            rw [heq, max_eq_right hw0] at h1; exact h1
          have hdiff : u ^ 2 - w ^ 2 ≤ (3699 / 10000 : ℝ) * t * Rbar := by
            have : u ^ 2 - w ^ 2 = (27 / 100 : ℝ) * Rbar * (2 * u - (27 / 100 : ℝ) * Rbar) := by dsimp only [w]; ring
            nlinarith [vp.hR_lo]
          nlinarith [vp.hR_lo, vp.ht_lo]
        · have hu_lt : u < (27 / 100 : ℝ) * Rbar := by dsimp only [w] at hw0; linarith
          nlinarith [vp.hR_lo, vp.ht_lo]
    set m := max 0 u
    have hA_le : (685 / 1000 : ℝ) * t ≤ m + (3 / 50 : ℝ) * e := by
      have : u ≤ m := le_max_right 0 u; dsimp only [u] at this; linarith
    have hA_sq : ((685 / 1000 : ℝ) * t) ^ 2 ≤ (m + (3 / 50 : ℝ) * e) ^ 2 := by
      have h1 : 0 ≤ (685 / 1000 : ℝ) * t := by linarith [vp.ht_lo]
      nlinarith
    have hcs := sq_nonneg (m - 39 * ((3 / 50 : ℝ) * e))
    nlinarith
  -- Step 2: Combine (17/20) * OptA + (3/20) * OptB.
  have hPhiA : (muUParam * (2 * (mStar - epsParam) - 1) - mStar - 2 * mugParam * epsParam) * e
      + ((731991 / 1600000 : ℝ) - muUParam * (qStar * L)) * t ^ 2 - (351 / 2500 : ℝ) * e ^ 2
      ≤ PhiT s e t Rbar sq_val U_val g_val := by
    unfold PhiT; rw [vp.hU_eq]
    have hmuU := muUParam_nonneg; have hmug := mugParam_nonneg
    have h1 : 0 ≤ muUParam * Fbar := mul_nonneg hmuU vp.hF_lo
    have h2 : mugParam * Fbar ≤ mugParam * g_val := mul_le_mul_of_nonneg_left vp.hF_le_g hmug
    have h3 : (2 * muUParam + 2 * mugParam) * (mStar - epsParam) * e ≤ (2 * muUParam + 2 * mugParam) * s * e := by
      have : 0 ≤ (2 * muUParam + 2 * mugParam) * e := by positivity
      nlinarith [vp.hs_lo]
    linarith
  have hPhiB : (muUParam * ((809 / 500 : ℝ) * (mStar - epsParam) - 1) - mStar - 2 * mugParam * epsParam) * e
      + (731991 / 1600000 : ℝ) * t ^ 2 - (351 / 2500 : ℝ) * e ^ 2
      ≤ PhiT s e t Rbar sq_val U_val g_val := by
    unfold PhiT
    have hmuU := muUParam_nonneg; have hmug := mugParam_nonneg
    have hU := mul_le_mul_of_nonneg_left (show (809 / 500 : ℝ) * s * e - e ≤ U_val - e by linarith [vp.hU_bopp]) hmuU
    have h2 : mugParam * Fbar ≤ mugParam * g_val := mul_le_mul_of_nonneg_left vp.hF_le_g hmug
    have h3 : ((809 / 500 : ℝ) * muUParam + 2 * mugParam) * (mStar - epsParam) * e
        ≤ ((809 / 500 : ℝ) * muUParam + 2 * mugParam) * s * e := by
      have : 0 ≤ ((809 / 500 : ℝ) * muUParam + 2 * mugParam) * e := by positivity
      nlinarith [vp.hs_lo]
    linarith
  -- Step 3: Certify both combined coefficients are strictly positive!
  have ht2_pos : (0 : ℝ) < (731991 / 1600000 : ℝ) - (561 / 200 : ℝ) * (qStar * L) := by
    have ha2 : mem (ofRat 731991 1600000) (731991 / 1600000 : ℝ) := by convert mem_ofRat (p := 731991) (q := 1600000) (by norm_num)
    have h561 : mem (ofRat 561 200) (561 / 200 : ℝ) := by convert mem_ofRat (p := 561) (q := 200) (by norm_num)
    have hlt := lt_of_hi_lt_lo (mem_mul h561 mem_qLIv) ha2 (by decide)
    linarith
  have hc0_gt : (351 / 2500 : ℝ) * ((e1Cut : ℝ) / SCALE)
      < muUParam * ((19427 / 10000 : ℝ) * (mStar - epsParam) - 1) - mStar - 2 * (mugParam * epsParam) := by
    have h351 : mem (ofRat 351 2500) (351 / 2500 : ℝ) := by convert mem_ofRat (p := 351) (q := 2500) (by norm_num)
    have h19427 : mem (ofRat 19427 10000) (19427 / 10000 : ℝ) := by convert mem_ofRat (p := 19427) (q := 10000) (by norm_num)
    have hc0 := mem_sub (mem_sub (mem_mul mem_muUIv (mem_sub (mem_mul h19427 mem_mSubEpsIv) mem_ONE))
      validConstIv.hm_mem) (mem_mul (mem_ofInt 2) (mem_mul mem_muGIv mem_epsIv))
    have he1_mem := mem_mul h351 (mem_pt e1Cut)
    have hlt := lt_of_hi_lt_lo he1_mem hc0 (by decide)
    convert hlt using 1
  have hcomb : (muUParam * ((19427 / 10000 : ℝ) * (mStar - epsParam) - 1) - mStar - 2 * (mugParam * epsParam)
      - (351 / 2500 : ℝ) * e) * e
      + ((731991 / 1600000 : ℝ) - (561 / 200 : ℝ) * (qStar * L)) * t ^ 2
      ≤ PhiT s e t Rbar sq_val U_val g_val := by
    have hmu : (17 / 20 : ℝ) * muUParam = 561 / 200 := by unfold muUParam; norm_num
    have hlin : (17 / 20 : ℝ) * ((muUParam * (2 * (mStar - epsParam) - 1) - mStar - 2 * mugParam * epsParam) * e
          + ((731991 / 1600000 : ℝ) - muUParam * (qStar * L)) * t ^ 2 - (351 / 2500 : ℝ) * e ^ 2)
        + (3 / 20 : ℝ) * ((muUParam * ((809 / 500 : ℝ) * (mStar - epsParam) - 1) - mStar - 2 * mugParam * epsParam) * e
          + (731991 / 1600000 : ℝ) * t ^ 2 - (351 / 2500 : ℝ) * e ^ 2)
        = (muUParam * ((19427 / 10000 : ℝ) * (mStar - epsParam) - 1) - mStar - 2 * (mugParam * epsParam)
          - (351 / 2500 : ℝ) * e) * e
          + ((731991 / 1600000 : ℝ) - (561 / 200 : ℝ) * (qStar * L)) * t ^ 2 := by
      unfold muUParam; ring
    linarith
  have hlin_pos : 0 < (muUParam * ((19427 / 10000 : ℝ) * (mStar - epsParam) - 1) - mStar - 2 * (mugParam * epsParam)
      - (351 / 2500 : ℝ) * e) * e := mul_pos (by nlinarith) he0
  have ht2_nn : 0 ≤ ((731991 / 1600000 : ℝ) - (561 / 200 : ℝ) * (qStar * L)) * t ^ 2 :=
    mul_nonneg (le_of_lt ht2_pos) (sq_nonneg t)
  linarith

/-! ### Main Polytope Positivity Theorems -/

theorem polytope_G :
    ∀ wv omv : ℝ,
      ((wv = 0 ∧ omv = a0Param) ∨ (wv = 1 ∧ omv = a0Param) ∨ (wv = 1 ∧ omv = a0Param - 1)) →
      ∀ s e t Rbar Fbar U_val g_val sq_val : ℝ,
        ValidPoint s e t Rbar Fbar U_val g_val sq_val →
        zParam ≤ e →
        0 < PhiG wv omv s e t Rbar U_val g_val := by
  intro wv omv hv s e t Rbar Fbar U_val g_val sq_val vp he_z
  have hzLo_eq : zLoCut = zIv.lo := by decide
  have hLHi_eq : LHiCut = LN2.hi := by decide
  have he_mem : mem ⟨zLoCut, LHiCut⟩ e :=
    ⟨by rw [hzLo_eq]; exact le_trans mem_zIv.1 he_z, by rw [hLHi_eq]; exact le_trans vp.he_hi mem_LN2.2⟩
  have ht_mem : mem ⟨0, (SCALE : ℤ)⟩ t :=
    ⟨by simp [vp.ht_lo], by push_cast; rw [div_self SCALE_ne_zero]; exact vp.ht_hi⟩
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h1 := checkPolyTree_sound_y0
      (P := fun e' t' => e' = e → t' = t → 0 < PhiG ((0 : ℤ) : ℝ) ((3 : ℤ) / (8 : ℕ)) s e t Rbar U_val g_val)
      (fun Ix Iy w hy0 hok e' t' he' ht' heq1 heq2 => by
        subst heq1; subst heq2; exact leafOkG_sound (by norm_num) le_rfl rfl hy0 hok vp he' ht')
      le_rfl check_treeG1 he_mem ht_mem rfl rfl
    simpa [a0Param] using h1
  · have h2 := checkPolyTree_sound_y0
      (P := fun e' t' => e' = e → t' = t → 0 < PhiG ((1 : ℤ) : ℝ) ((3 : ℤ) / (8 : ℕ)) s e t Rbar U_val g_val)
      (fun Ix Iy w hy0 hok e' t' he' ht' heq1 heq2 => by
        subst heq1; subst heq2; exact leafOkG_sound (by norm_num) (by omega) rfl hy0 hok vp he' ht')
      le_rfl check_treeG2 he_mem ht_mem rfl rfl
    simpa [a0Param] using h2
  · have h3 := checkPolyTree_sound_y0
      (P := fun e' t' => e' = e → t' = t → 0 < PhiG ((1 : ℤ) : ℝ) ((-5 : ℤ) / (8 : ℕ)) s e t Rbar U_val g_val)
      (fun Ix Iy w hy0 hok e' t' he' ht' heq1 heq2 => by
        subst heq1; subst heq2; exact leafOkG_sound (by norm_num) (by omega) rfl hy0 hok vp he' ht')
      le_rfl check_treeG3 he_mem ht_mem rfl rfl
    have heq : (a0Param - 1 : ℝ) = ((-5 : ℤ) : ℝ) / (8 : ℕ) := by unfold a0Param; norm_num
    rw [heq]; simpa using h3

theorem polytope_T :
    ∀ s e t Rbar Fbar U_val g_val sq_val : ℝ,
      ValidPoint s e t Rbar Fbar U_val g_val sq_val →
      0 < e → e ≤ zParam →
      0 < PhiT s e t Rbar sq_val U_val g_val := by
  intro s e t Rbar Fbar U_val g_val sq_val vp he0 hez
  rcases le_or_gt e ((e1Cut : ℝ) / SCALE) with hsmall | hbig
  · exact PhiT_pos_small_e vp he0 hsmall
  · have hzHi_eq : zHiCut = zIv.hi := by decide
    have he_mem : mem ⟨e1Cut, zHiCut⟩ e :=
      ⟨le_of_lt hbig, by rw [hzHi_eq]; exact le_trans hez mem_zIv.2⟩
    have ht_mem : mem ⟨0, (SCALE : ℤ)⟩ t :=
      ⟨by simp [vp.ht_lo], by push_cast; rw [div_self SCALE_ne_zero]; exact vp.ht_hi⟩
    exact checkPolyTree_sound_y0
      (P := fun e' t' => e' = e → t' = t → 0 < PhiT s e t Rbar sq_val U_val g_val)
      (fun Ix Iy w hy0 hok e' t' he' ht' heq1 heq2 => by
        subst heq1; subst heq2; exact leafOkT_sound hy0 hok vp he' ht')
      le_rfl check_treeT he_mem ht_mem rfl rfl

end UCBound.Cert
