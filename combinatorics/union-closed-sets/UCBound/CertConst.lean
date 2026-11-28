module

public import UCBound.IntervalOps

@[expose] public section

/-!
# Certified 50-bit Interval Enclosures of All Proof Constants

Computes and kernel-certifies `constIv : ConstIv` (stored as literal 50-bit integer intervals
for O(1) lookup in downstream `decide` proofs), together with:
- `validConstIv : ValidConstIv constIv`
- `cStar_add_eps_gt : (1533 : ℝ) / 4000 < cStar + epsParam`
- `tau_pos : 0 < tau` and `tau_lt_half : tau < 1 / 2`
- `DParam_pos : 0 < DParam` and `DParam_lt_kappa : DParam < kappaParam`
-/

namespace UCBound.Cert

open UCBound UCBound.Iv

/-- Executable interval enclosure of `rootEq (a / SCALE) = -(1 - x) log(1 - x) - x log(1 + x)`. -/
def rootEqPt (a : ℕ) : Interval :=
  let x : Interval := ⟨(a : ℤ), (a : ℤ)⟩
  let omx : Interval := ⟨(SCALE : ℤ) - (a : ℤ), (SCALE : ℤ) - (a : ℤ)⟩
  sub (neg (mul omx (logNat (SCALE - a)))) (mul x (logNat (SCALE + a)))

lemma mem_rootEqPt {a : ℕ} (ha0 : 0 < a) (ha1 : a < SCALE) :
    mem (rootEqPt a) (rootEq ((a : ℝ) / SCALE)) := by
  have hx : mem ⟨(a : ℤ), (a : ℤ)⟩ ((a : ℝ) / SCALE) := ⟨le_rfl, le_rfl⟩
  have homx : mem ⟨(SCALE : ℤ) - (a : ℤ), (SCALE : ℤ) - (a : ℤ)⟩ (1 - (a : ℝ) / SCALE) := by
    unfold mem; push_cast
    rw [sub_div, div_self SCALE_ne_zero]; exact ⟨le_rfl, le_rfl⟩
  have h1mx_eq : ((SCALE - a : ℕ) : ℝ) / SCALE = 1 - (a : ℝ) / SCALE := by
    rw [Nat.cast_sub (le_of_lt ha1), sub_div, div_self SCALE_ne_zero]
  have h1px_eq : ((SCALE + a : ℕ) : ℝ) / SCALE = 1 + (a : ℝ) / SCALE := by
    rw [Nat.cast_add, add_div, div_self SCALE_ne_zero]
  have hlog1 : mem (logNat (SCALE - a)) (Real.log (1 - (a : ℝ) / SCALE)) := by
    rw [← h1mx_eq]; exact mem_logNat (by omega)
  have hlog2 : mem (logNat (SCALE + a)) (Real.log (1 + (a : ℝ) / SCALE)) := by
    rw [← h1px_eq]; exact mem_logNat (by omega)
  unfold rootEqPt rootEq
  have hres := mem_sub (mem_neg (mem_mul homx hlog1)) (mem_mul hx hlog2)
  convert hres using 1; ring

/-- Precomputed literal 50-bit constant intervals for O(1) kernel lookup in downstream `decide` proofs. -/
def constIv : ConstIv :=
  { r := ⟨777892958667769, 777892958667799⟩
    m := ⟨694809428314581, 694809428314604⟩
    q := ⟨263718949786538, 263718949786584⟩
    hr := ⟨696225470343970, 696225470344021⟩
    p := ⟨-905636149243082, -905636149242886⟩
    c := ⟨1643450492846251, 1643450492846533⟩
    tau := ⟨559093484481094, 559093484482190⟩
    gamma := ⟨1007696731879656, 1007696731879770⟩
    alpha := ⟨2378683000248486, 2378683000248900⟩
    t0 := ⟨83083530353165, 83083530353218⟩
    bm := ⟨366681688293144, 366681688293358⟩
    D := ⟨326610046721369, 326610046721613⟩
    eStar := ⟨621864506726211, 621864506726303⟩
    beta := ⟨288438248582077, 288438248582705⟩
    b0 := ⟨875735876775000, 875735876778000⟩
    W := ⟨506281869847727, 506281869854903⟩
    eta := ⟨703011689948014, 703011689963157⟩
    sqrtL := ⟨937373159143848, 937373159143850⟩ }

/-- Helper: `a < b` on scaled-integer intervals implies `x < y` for `x ∈ I, y ∈ J`. -/
lemma lt_of_hi_lt_lo {I J : Interval} {x y : ℝ} (hx : mem I x) (hy : mem J y) (h : I.hi < J.lo) :
    x < y := by
  have h1 : (I.hi : ℝ) / SCALE < (J.lo : ℝ) / SCALE :=
    div_lt_div_of_pos_right (by exact_mod_cast h) SCALE_pos
  linarith [hx.2, hy.1]

/-- Helper: `0 < I.lo` implies `0 < x` for `x ∈ I`. -/
lemma pos_of_lo_pos {I : Interval} {x : ℝ} (hx : mem I x) (h : 0 < I.lo) : 0 < x := by
  have h1 : (0 : ℝ) < (I.lo : ℝ) / SCALE := div_pos (by exact_mod_cast h) SCALE_pos
  linarith [hx.1]

/-- Helper: transport `mem` across a decided interval equality `I = J`. -/
private lemma mem_of_eq {I J : Interval} {x : ℝ} (heq : I = J) (h : mem J x) : mem I x :=
  heq ▸ h

/-- Certify `rStar ∈ constIv.r` via sign change of `rootEq`. -/
lemma mem_rStar : mem constIv.r rStar := by
  have hlo_pos : 0 < (rootEqPt 777892958667769).lo := by decide
  have hhi_neg : (rootEqPt 777892958667799).hi < 0 := by decide
  have hmem_lo := mem_rootEqPt (a := 777892958667769) (by norm_num) (by unfold SCALE; norm_num)
  have hmem_hi := mem_rootEqPt (a := 777892958667799) (by norm_num) (by unfold SCALE; norm_num)
  have hr_lo_pos : 0 < rootEq ((777892958667769 : ℝ) / SCALE) := pos_of_lo_pos hmem_lo hlo_pos
  have hr_hi_neg : rootEq ((777892958667799 : ℝ) / SCALE) < 0 := by
    have h1 : ((rootEqPt 777892958667799).hi : ℝ) / SCALE < 0 :=
      div_neg_of_neg_of_pos (by exact_mod_cast hhi_neg) SCALE_pos
    linarith [hmem_hi.2]
  have hlo_Icc : ((777892958667769 : ℝ) / SCALE) ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    unfold SCALE; constructor <;> norm_num
  have hhi_Icc : ((777892958667799 : ℝ) / SCALE) ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    unfold SCALE; constructor <;> norm_num
  have hlt1 := lt_rStar_of_rootEq_pos hlo_Icc hr_lo_pos
  have hlt2 := rStar_lt_of_rootEq_neg hhi_Icc hr_hi_neg
  unfold constIv mem; dsimp only
  exact ⟨le_of_lt (by push_cast; exact hlt1), le_of_lt (by push_cast; exact hlt2)⟩

/-- Certify all 18 constant enclosures in `constIv`, one flat `decide` per field. -/
theorem validConstIv : ValidConstIv constIv := by
  have hr_m := mem_rStar
  have hm_m : mem constIv.m mStar := by
    apply mem_of_eq (show constIv.m = add (ofRat 1 2)
      (divPos (mul (sub ONE constIv.r) (log (add ONE constIv.r))) (mul (ofInt 2) LN2)) by decide)
    unfold mStar
    have h1pr := mem_add mem_ONE hr_m
    have hlog := mem_log h1pr (by decide)
    have hnum := mem_mul (mem_sub mem_ONE hr_m) hlog
    have hden := mem_mul (mem_ofInt 2) mem_LN2
    have hdiv := mem_divPos hnum hden (by decide)
    have hres := mem_add (mem_ofRat (p := 1) (q := 2) (by norm_num)) hdiv
    convert hres using 1; push_cast; rfl
  have hq_m : mem constIv.q qStar := by
    apply mem_of_eq (show constIv.q = sub (mul (ofInt 2) constIv.m) ONE by decide)
    unfold qStar
    have hres := mem_sub (mem_mul (mem_ofInt 2) hm_m) mem_ONE
    convert hres using 1
  have hhr_m : mem constIv.hr UCBound.hr := by
    apply mem_of_eq (show constIv.hr = hIv constIv.r by decide)
    exact mem_hIv hr_m (le_of_lt rStar_pos) (le_of_lt rStar_lt_one)
  have hp_m : mem constIv.p pStar := by
    apply mem_of_eq (show constIv.p = hpIv constIv.r by decide)
    exact mem_hpIv hr_m (by decide) (by decide)
  have hc_m : mem constIv.c cParam := by
    apply mem_of_eq (show constIv.c = sub constIv.r (divNeg constIv.hr constIv.p) by decide)
    exact mem_sub hr_m (mem_divNeg hhr_m hp_m (by decide))
  have htau_m : mem constIv.tau tau := by
    apply mem_of_eq (show constIv.tau = divPos (sub (ofRat 1 2) (sq constIv.r))
      (mul (sq constIv.r) (sq (sub ONE constIv.r))) by decide)
    unfold tau
    have hr2 := mem_sq hr_m
    have homr2 := mem_sq (mem_sub mem_ONE hr_m)
    have hres := mem_divPos (mem_sub (mem_ofRat (p := 1) (q := 2) (by norm_num)) hr2)
      (mem_mul hr2 homr2) (by decide)
    convert hres using 1; push_cast; rfl
  have hgamma_m : mem constIv.gamma gamma := by
    apply mem_of_eq (show constIv.gamma = divPos constIv.hr constIv.r by decide)
    exact mem_divPos hhr_m hr_m (by decide)
  have halpha_m : mem constIv.alpha alpha := by
    apply mem_of_eq (show constIv.alpha = sub ONE (divNeg constIv.gamma constIv.p) by decide)
    exact mem_sub mem_ONE (mem_divNeg hgamma_m hp_m (by decide))
  have ht0_m : mem constIv.t0 t0 := by
    apply mem_of_eq (show constIv.t0 = sub constIv.r constIv.m by decide)
    exact mem_sub hr_m hm_m
  have hpa_m : mem (mul constIv.p constIv.alpha) (pStar * alpha) := mem_mul hp_m halpha_m
  have hbm_m : mem constIv.bm bm := by
    apply mem_of_eq (show constIv.bm = divNeg (mul (neg constIv.hr) constIv.gamma)
      (mul constIv.p constIv.alpha) by decide)
    unfold bm
    have hres := mem_divNeg (mem_mul (mem_neg hhr_m) hgamma_m) hpa_m (by decide)
    convert hres using 1
  have hD_m : mem constIv.D DParam := by
    apply mem_of_eq (show constIv.D = sub (divNeg (neg constIv.hr) (mul constIv.p constIv.alpha)) constIv.t0 by decide)
    exact mem_sub (mem_divNeg (mem_neg hhr_m) hpa_m (by decide)) ht0_m
  have heStar_m : mem constIv.eStar eStar := by
    apply mem_of_eq (show constIv.eStar = mul constIv.gamma constIv.m by decide)
    exact mem_mul hgamma_m hm_m
  have hkappa_m : mem (ofRat 39 100) kappaParam := by
    unfold kappaParam; convert mem_ofRat (p := 39) (q := 100) (by norm_num)
  have ha0_m : mem (ofRat 3 8) a0Param := by
    unfold a0Param; convert mem_ofRat (p := 3) (q := 8) (by norm_num)
  have hbeta_m : mem constIv.beta betaParam := by
    apply mem_of_eq (show constIv.beta = sub ONE (divPos constIv.D (ofRat 39 100)) by decide)
    exact mem_sub mem_ONE (mem_divPos hD_m hkappa_m (by decide))
  have hb0_m : mem constIv.b0 b0Param := by
    have hlog_a0 : mem (log (ofRat 3 8)) (Real.log a0Param) := mem_log ha0_m (by decide)
    have hrhs : mem (mul constIv.beta (log (ofRat 3 8))) (betaParam * Real.log a0Param) :=
      mem_mul hbeta_m hlog_a0
    have hlog_lo := mem_logNat (a := 875735876775000) (by norm_num)
    have hlog_hi := mem_logNat (a := 875735876778000) (by norm_num)
    have hchk1 : (logNat 875735876775000).hi < (mul constIv.beta (log (ofRat 3 8))).lo := by decide
    have hchk2 : (mul constIv.beta (log (ofRat 3 8))).hi < (logNat 875735876778000).lo := by decide
    have hlt1 := lt_of_hi_lt_lo hlog_lo hrhs hchk1
    have hlt2 := lt_of_hi_lt_lo hrhs hlog_hi hchk2
    have hlog_b0 : Real.log b0Param = betaParam * Real.log a0Param := by
      unfold b0Param; rw [Real.log_rpow a0Param_pos]
    have hb0_pos : 0 < b0Param := Real.rpow_pos_of_pos a0Param_pos _
    have hlo_pos : (0 : ℝ) < (875735876775000 : ℝ) / SCALE := by unfold SCALE; positivity
    have hhi_pos : (0 : ℝ) < (875735876778000 : ℝ) / SCALE := by unfold SCALE; positivity
    have h1 : (875735876775000 : ℝ) / SCALE < b0Param := by
      rw [← Real.log_lt_log_iff hlo_pos hb0_pos, hlog_b0]; simpa using hlt1
    have h2 : b0Param < (875735876778000 : ℝ) / SCALE := by
      rw [← Real.log_lt_log_iff hb0_pos hhi_pos, hlog_b0]; simpa using hlt2
    unfold constIv mem; dsimp only
    exact ⟨le_of_lt (by push_cast; exact h1), le_of_lt (by push_cast; exact h2)⟩
  have hW_m : mem constIv.W WParam := by
    apply mem_of_eq (show constIv.W = divPos (sub (ofRat 39 100) constIv.D) (sub ONE constIv.b0) by decide)
    exact mem_divPos (mem_sub hkappa_m hD_m) (mem_sub mem_ONE hb0_m) (by decide)
  have heta_m : mem constIv.eta etaParam := by
    apply mem_of_eq (show constIv.eta = divPos (mul (divPos (sub (ofRat 39 100) constIv.D) constIv.D)
      (sub constIv.b0 (ofRat 3 8))) (sub ONE constIv.b0) by decide)
    exact mem_divPos (mem_mul (mem_divPos (mem_sub hkappa_m hD_m) hD_m (by decide))
      (mem_sub hb0_m ha0_m)) (mem_sub mem_ONE hb0_m) (by decide)
  have hsqrtL_m : mem constIv.sqrtL (Real.sqrt L) := by
    have hlo : constIv.sqrtL.lo = (sqrt LN2).lo := by decide
    have hhi : constIv.sqrtL.hi = (sqrt LN2).hi := by decide
    have heq : constIv.sqrtL = sqrt LN2 := by cases h1 : constIv.sqrtL; cases h2 : sqrt LN2; simp_all
    exact mem_of_eq heq (mem_sqrt mem_LN2 (le_of_lt L_pos))
  have htau_pos : 0 < tau := pos_of_lo_pos htau_m (by decide)
  have htau_lt_half : tau < 1 / 2 := by
    have hhalf : mem (ofRat 1 2) (1 / 2 : ℝ) := by
      convert mem_ofRat (p := 1) (q := 2) (by norm_num); norm_num
    exact lt_of_hi_lt_lo htau_m hhalf (by decide)
  exact {
    hr_mem := hr_m, hm_mem := hm_m, hq_mem := hq_m, hhr_mem := hhr_m, hp_mem := hp_m, hc_mem := hc_m,
    htau_mem := htau_m, hgamma_mem := hgamma_m, halpha_mem := halpha_m, ht0_mem := ht0_m,
    hbm_mem := hbm_m, hD_mem := hD_m, heStar_mem := heStar_m, hbeta_mem := hbeta_m,
    hb0_mem := hb0_m, hW_mem := hW_m, heta_mem := heta_m, hsqrtL_mem := hsqrtL_m,
    htau_pos := htau_pos, htau_lt_half := htau_lt_half
  }

/-- Certified numerical bound: `1533 / 4000 = 0.38325 < cStar + epsParam`. -/
theorem cStar_add_eps_gt : (1533 : ℝ) / 4000 < cStar + epsParam := by
  have hm := validConstIv.hm_mem
  have heps : mem (ofRat 365 1000000) epsParam := by
    unfold epsParam; convert mem_ofRat (p := 365) (q := 1000000) (by norm_num)
  have hce : mem (add (sub ONE constIv.m) (ofRat 365 1000000)) (cStar + epsParam) := by
    unfold cStar; exact mem_add (mem_sub mem_ONE hm) heps
  have htarget : mem (ofRat 1533 4000) ((1533 : ℝ) / 4000) := by
    convert mem_ofRat (p := 1533) (q := 4000) (by norm_num)
  exact lt_of_hi_lt_lo htarget hce (by decide)

theorem tau_pos : 0 < tau := validConstIv.htau_pos
theorem tau_lt_half : tau < 1 / 2 := validConstIv.htau_lt_half

theorem DParam_pos : 0 < DParam := pos_of_lo_pos validConstIv.hD_mem (by decide)

theorem DParam_lt_kappa : DParam < kappaParam := by
  have hkappa : mem (ofRat 39 100) kappaParam := by
    unfold kappaParam; convert mem_ofRat (p := 39) (q := 100) (by norm_num)
  exact lt_of_hi_lt_lo validConstIv.hD_mem hkappa (by decide)

end UCBound.Cert
