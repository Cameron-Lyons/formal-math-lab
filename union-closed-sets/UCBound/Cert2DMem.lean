module

public import UCBound.Cert2DHelpers

@[expose] public section

/-!
# Subinterval-Point Soundness Helpers and Shared 2D Evaluators

Provides `mem_fastFx_pt` directly from `fGuard2DF X Y` whenever `X.lo ≤ mx ≤ X.hi`,
plus strict CBV interval evaluators and leaf predicates for `F_R`, `F_v`, and `F_sim`.
-/

namespace UCBound.Cert2D

open UCBound UCBound.Iv UCBound.Cert UCBound.FastIv

lemma mem_sub_pt_le {X : Interval} {mx : ℤ} (hlo : X.lo ≤ mx) (hhi : mx ≤ X.hi) :
    ∀ u, mem (pt mx) u → mem X u := fun u hu => by
  have hS := SCALE_pos
  exact ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hS)) hu.1,
         le_trans hu.2 (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hS))⟩

private lemma fdiv_le_fdiv_of_le {a a' : ℤ} {b : ℕ} (hb : 0 < b) (h : a ≤ a') :
    fdiv a b ≤ fdiv a' b := by
  unfold fdiv; exact Int.ediv_le_ediv (Nat.cast_pos.mpr hb) h

private lemma cdiv_le_cdiv_of_le {a a' : ℤ} {b : ℕ} (hb : 0 < b) (h : a ≤ a') :
    cdiv a b ≤ cdiv a' b := by
  unfold cdiv
  have h1 : (-a') / (b : ℤ) ≤ (-a) / (b : ℤ) := Int.ediv_le_ediv (Nat.cast_pos.mpr hb) (by omega)
  omega

private lemma fdiv_le_cdiv_of_le {a a' : ℤ} {b : ℕ} (hb : 0 < b) (h : a ≤ a') :
    fdiv a b ≤ cdiv a' b := by
  have h1 : (fdiv a b : ℝ) ≤ (a : ℝ) / (b : ℝ) := fdiv_le a hb
  have h2 : (a : ℝ) / (b : ℝ) ≤ (a' : ℝ) / (b : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg b)
  have h3 : (a' : ℝ) / (b : ℝ) ≤ (cdiv a' b : ℝ) := le_cdiv a' hb
  exact_mod_cast le_trans h1 (le_trans h2 h3)

private lemma mul_lo_le_hi (A B : Interval) : (mul A B).lo ≤ (mul A B).hi := by
  unfold mul; dsimp only
  exact fdiv_le_cdiv_of_le SCALE_pos_nat (by omega)

lemma mul_mono {A A' B : Interval} (hlo : A'.lo ≤ A.lo) (hhi : A.hi ≤ A'.hi) (hAle : A.lo ≤ A.hi)
    (hBle : B.lo ≤ B.hi) :
    (mul A' B).lo ≤ (mul A B).lo ∧ (mul A B).hi ≤ (mul A' B).hi := by
  have hbd : ∀ x y : ℤ, A.lo ≤ x → x ≤ A.hi → B.lo ≤ y → y ≤ B.hi →
      min (min (A'.lo * B.lo) (A'.lo * B.hi)) (min (A'.hi * B.lo) (A'.hi * B.hi)) ≤ x * y ∧
      x * y ≤ max (max (A'.lo * B.lo) (A'.lo * B.hi)) (max (A'.hi * B.lo) (A'.hi * B.hi)) := by
    intro x y hx1 hx2 hy1 hy2
    have hx1' : A'.lo ≤ x := le_trans hlo hx1
    have hx2' : x ≤ A'.hi := le_trans hx2 hhi
    constructor
    · by_cases hy : 0 ≤ y
      · have h1 : A'.lo * y ≤ x * y := mul_le_mul_of_nonneg_right hx1' hy
        by_cases ha : 0 ≤ A'.lo
        · exact le_trans (min_le_of_left_le (min_le_left _ _)) (le_trans (mul_le_mul_of_nonneg_left hy1 ha) h1)
        · exact le_trans (min_le_of_left_le (min_le_right _ _)) (le_trans (mul_le_mul_of_nonpos_left hy2 (le_of_not_ge ha)) h1)
      · have h1 : A'.hi * y ≤ x * y := mul_le_mul_of_nonpos_right hx2' (le_of_not_ge hy)
        by_cases ha : 0 ≤ A'.hi
        · exact le_trans (min_le_of_right_le (min_le_left _ _)) (le_trans (mul_le_mul_of_nonneg_left hy1 ha) h1)
        · exact le_trans (min_le_of_right_le (min_le_right _ _)) (le_trans (mul_le_mul_of_nonpos_left hy2 (le_of_not_ge ha)) h1)
    · by_cases hy : 0 ≤ y
      · have h1 : x * y ≤ A'.hi * y := mul_le_mul_of_nonneg_right hx2' hy
        by_cases ha : 0 ≤ A'.hi
        · exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_left hy2 ha) (le_max_of_le_right (le_max_right _ _)))
        · exact le_trans h1 (le_trans (mul_le_mul_of_nonpos_left hy1 (le_of_not_ge ha)) (le_max_of_le_right (le_max_left _ _)))
      · have h1 : x * y ≤ A'.lo * y := mul_le_mul_of_nonpos_right hx1' (le_of_not_ge hy)
        by_cases ha : 0 ≤ A'.lo
        · exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_left hy2 ha) (le_max_of_le_left (le_max_right _ _)))
        · exact le_trans h1 (le_trans (mul_le_mul_of_nonpos_left hy1 (le_of_not_ge ha)) (le_max_of_le_left (le_max_left _ _)))
  have h1 := hbd A.lo B.lo le_rfl hAle le_rfl hBle
  have h2 := hbd A.lo B.hi le_rfl hAle hBle le_rfl
  have h3 := hbd A.hi B.lo hAle le_rfl le_rfl hBle
  have h4 := hbd A.hi B.hi hAle le_rfl hBle le_rfl
  have hmin : min (min (A'.lo * B.lo) (A'.lo * B.hi)) (min (A'.hi * B.lo) (A'.hi * B.hi))
      ≤ min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)) := by omega
  have hmax : max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi))
      ≤ max (max (A'.lo * B.lo) (A'.lo * B.hi)) (max (A'.hi * B.lo) (A'.hi * B.hi)) := by omega
  unfold mul
  dsimp only
  constructor
  · exact fdiv_le_fdiv_of_le SCALE_pos_nat hmin
  · exact cdiv_le_cdiv_of_le SCALE_pos_nat hmax

lemma mul_comm_iv (X Y : Interval) : mul X Y = mul Y X := by
  unfold mul; dsimp only
  have h1 : X.lo * Y.lo = Y.lo * X.lo := mul_comm _ _
  have h2 : X.lo * Y.hi = Y.hi * X.lo := mul_comm _ _
  have h3 : X.hi * Y.lo = Y.lo * X.hi := mul_comm _ _
  have h4 : X.hi * Y.hi = Y.hi * X.hi := mul_comm _ _
  have hmin : min (min (X.lo * Y.lo) (X.lo * Y.hi)) (min (X.hi * Y.lo) (X.hi * Y.hi)) =
      min (min (Y.lo * X.lo) (Y.lo * X.hi)) (min (Y.hi * X.lo) (Y.hi * X.hi)) := by omega
  have hmax : max (max (X.lo * Y.lo) (X.lo * Y.hi)) (max (X.hi * Y.lo) (X.hi * Y.hi)) =
      max (max (Y.lo * X.lo) (Y.lo * X.hi)) (max (Y.hi * X.lo) (Y.hi * X.hi)) := by omega
  rw [hmin, hmax]

lemma mem_fastFx_pt {X Y : Interval} (hg : fGuard2DF X Y = true)
    {mx : ℤ} (hlo : X.lo ≤ mx) (hhi : mx ≤ X.hi)
    {v : ℝ} (hv : mem Y v) :
    mem (fastFx Y (pt mx)) (Fx_fun v ((mx : ℝ) / SCALE)) := by
  have hS := SCALE_pos
  unfold fGuard2DF at hg
  simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hgX, hgY⟩, ⟨hxy0, hxy1⟩⟩ := hg
  have hgX' := hgX; unfold fGuardD1 at hgX'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgX'
  have hgY' := hgY; unfold fGuardD1 at hgY'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgY'
  have hYle : Y.lo ≤ Y.hi := hgY'.1.1.1.1.1.1.2
  have hmxX : mem X ((mx : ℝ) / SCALE) := mem_sub_pt_le hlo hhi _ (mem_pt mx)
  have ⟨hx0, hx1⟩ := fGuardD1_bounds hgX hmxX
  have ⟨hy0, hy1⟩ := fGuardD1_bounds hgY hv
  have hmul_sub := mul_mono (A := pt mx) (A' := X) (B := Y) hlo hhi le_rfl hYle
  rw [mul_comm_iv (pt mx) Y] at hmul_sub
  have hxy0' : 0 < (clamp01 (mul Y (pt mx))).lo := by
    unfold clamp01 at hxy0 ⊢; dsimp only at hxy0 ⊢; omega
  have hxy1' : 0 < (sub ONE (clamp01 (mul Y (pt mx)))).lo := by
    unfold sub ONE clamp01 at hxy1 ⊢; dsimp only at hxy1 ⊢; omega
  have hvy := mem_clamp01 (mem_mul hv (mem_pt mx)) (by positivity) (by nlinarith)
  have hres := mem_sub (mem_add (mem_mul (mem_pt mx) (mem_sub (mem_fastHp hvy hxy0' hxy1')
      (mem_fastHp hv hgY'.1.1.1.1.1.1.1 hgY'.1.1.1.1.1.2)))
    (mem_mul mem_qLIv (mem_mul (mem_fastPhiP_of_guard hgY hv) (mem_fastPhi validConstIv (mem_pt mx) (le_of_lt hx0) (le_of_lt hx1)))))
    (mem_fastH (mem_pt mx) (le_of_lt hx0) (le_of_lt hx1))
  have heq : (mx : ℝ) / SCALE * (hp (v * ((mx : ℝ) / SCALE)) - hp v)
      + qStar * L * (phiP v * phi ((mx : ℝ) / SCALE)) - h ((mx : ℝ) / SCALE) = Fx_fun v ((mx : ℝ) / SCALE) := by
    unfold Fx_fun; ring
  unfold fastFx; simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, fadd_eq]
  rwa [heq] at hres

/-! ### Shared 2D Interval Evaluators & Predicates (Strict CBV) -/

def cFR_11 : Interval := ofRat 11 200
def G_FR (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fastH X) fun hX => ivCBV (fastH Y) fun hY =>
  ivCBV (fastPhi constIv X) fun phX => ivCBV (fastPhi constIv Y) fun phY =>
  fsub (fastF_of constIv X Y hX hY phX phY)
       (fmul cFR_11 (fadd (fmul phX (fastR_of constIv Y hY phY)) (fmul phY (fastR_of constIv X hX phX))))
def Gx_FR (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fastHp X) fun hpX => ivCBV (fastPhiP X) fun phpX =>
  ivCBV (fastH Y) fun hY => ivCBV (fastPhi constIv Y) fun phY =>
  fsub (fastFx_of X Y hpX phpX hY phY)
       (fmul cFR_11 (fadd (fmul phpX (fastR_of constIv Y hY phY)) (fmul phY (fastRP_of X hpX phpX))))
def Hxx_FR (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  fsub (fastFxx X Y) (fmul cFR_11 (fadd (fmul (fastPhiPP X) (fastR constIv Y)) (fmul (fastPhi constIv Y) (fastRPP X))))
def Hxy_FR (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  fsub (fastFxy X Y) (fmul cFR_11 (fadd (fmul (fastPhiP X) (fastRP Y)) (fmul (fastPhiP Y) (fastRP X))))
def okFR (w : LeafW) (X Y : Interval) : Bool :=
  match w with
  | .skip => decide (Y.hi < X.lo)
  | .hess => false
  | _ => fGuard2DF X Y && centered2DWPos G_FR Gx_FR (fun U V => Gx_FR V U) w X Y

def okFRHess (w : LeafW) (X Y : Interval) : Bool :=
  match w with
  | .skip => decide (Y.hi < X.lo)
  | .hess => fGuard2DFHess X Y && hess2DPD (Hxx_FR X Y) (Hxx_FR Y X) (Hxy_FR X Y)
  | _ => false

def cFv_21 : Interval := ofRat 21 100
def G_Fv (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fastH X) fun hX => ivCBV (fastH Y) fun hY =>
  ivCBV (fastPhi constIv X) fun phX => ivCBV (fastPhi constIv Y) fun phY =>
  fsub (fastF_of constIv X Y hX hY phX phY)
       (fmul cFv_21 (fadd (fmul (fsq (fastV_of constIv hX phX)) phY) (fmul (fsq (fastV_of constIv hY phY)) phX)))
def Gx_Fv (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fastHp X) fun hpX => ivCBV (fastPhiP X) fun phpX =>
  ivCBV (fastH Y) fun hY => ivCBV (fastPhi constIv Y) fun phY =>
  fsub (fastFx_of X Y hpX phpX hY phY)
       (fmul cFv_21 (fadd (fmul (fmul (ofInt 2) (fmul (fastV constIv X) (fastVP_of hpX phpX))) phY)
                          (fmul (fsq (fastV_of constIv hY phY)) phpX)))
def Hxx_Fv (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  fsub (fastFxx X Y) (fmul cFv_21 (fadd (fmul (fmul (ofInt 2) (fadd (fsq (fastVP X)) (fmul (fastV constIv X) (fastVPP X)))) (fastPhi constIv Y)) (fmul (fsq (fastV constIv Y)) (fastPhiPP X))))
def Hxy_Fv (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  fsub (fastFxy X Y) (fmul cFv_21 (fadd (fmul (fmul (ofInt 2) (fmul (fastV constIv X) (fastVP X))) (fastPhiP Y)) (fmul (fmul (ofInt 2) (fmul (fastV constIv Y) (fastVP Y))) (fastPhiP X))))
def okFv (w : LeafW) (X Y : Interval) : Bool :=
  match w with
  | .skip => decide (Y.hi < X.lo)
  | .hess => false
  | _ => fGuard2DF X Y && centered2DWPos G_Fv Gx_Fv (fun U V => Gx_Fv V U) w X Y

def okFvHess (w : LeafW) (X Y : Interval) : Bool :=
  match w with
  | .skip => decide (Y.hi < X.lo)
  | .hess => fGuard2DFHess X Y && hess2DPD (Hxx_Fv X Y) (Hxx_Fv Y X) (Hxy_Fv X Y)
  | _ => false

def cFsim_3 : Interval := ofRat 3 100
def cFsim_13 : Interval := ofRat 13 100
def G_Fsim (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fastH X) fun hX => ivCBV (fastH Y) fun hY =>
  ivCBV (fastPhi constIv X) fun phX => ivCBV (fastPhi constIv Y) fun phY =>
  fsub (fsub (fastF_of constIv X Y hX hY phX phY)
             (fmul cFsim_3 (fadd (fmul phX (fastR_of constIv Y hY phY)) (fmul phY (fastR_of constIv X hX phX)))))
       (fmul cFsim_13 (fadd (fmul (fsq (fastV_of constIv hX phX)) phY) (fmul (fsq (fastV_of constIv hY phY)) phX)))
def Gx_Fsim (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fastHp X) fun hpX => ivCBV (fastPhiP X) fun phpX =>
  ivCBV (fastH Y) fun hY => ivCBV (fastPhi constIv Y) fun phY =>
  fsub (fsub (fastFx_of X Y hpX phpX hY phY)
             (fmul cFsim_3 (fadd (fmul phpX (fastR_of constIv Y hY phY)) (fmul phY (fastRP_of X hpX phpX)))))
       (fmul cFsim_13 (fadd (fmul (fmul (ofInt 2) (fmul (fastV constIv X) (fastVP_of hpX phpX))) phY)
                            (fmul (fsq (fastV_of constIv hY phY)) phpX)))
def Hxx_Fsim (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fastPhiPP X) fun phppX => ivCBV (fastPhi constIv Y) fun phY =>
  fsub (fsub (fastFxx X Y) (fmul cFsim_3 (fadd (fmul phppX (fastR constIv Y)) (fmul phY (fastRPP X)))))
       (fmul cFsim_13 (fadd (fmul (fmul (ofInt 2) (fadd (fsq (fastVP X)) (fmul (fastV constIv X) (fastVPP X)))) phY) (fmul (fsq (fastV constIv Y)) phppX)))
def Hxy_Fsim (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fastPhiP X) fun phpX => ivCBV (fastPhiP Y) fun phpY =>
  fsub (fsub (fastFxy X Y) (fmul cFsim_3 (fadd (fmul phpX (fastRP Y)) (fmul phpY (fastRP X)))))
       (fmul cFsim_13 (fadd (fmul (fmul (ofInt 2) (fmul (fastV constIv X) (fastVP X))) phpY) (fmul (fmul (ofInt 2) (fmul (fastV constIv Y) (fastVP Y))) phpX)))
def okFsim (w : LeafW) (X Y : Interval) : Bool :=
  match w with
  | .skip => decide (Y.hi < X.lo)
  | .hess => false
  | _ => fGuard2DF X Y && centered2DWPos G_Fsim Gx_Fsim (fun U V => Gx_Fsim V U) w X Y

def okFsimHess (w : LeafW) (X Y : Interval) : Bool :=
  match w with
  | .skip => decide (Y.hi < X.lo)
  | .hess => fGuard2DFHess X Y && hess2DPD (Hxx_Fsim X Y) (Hxx_Fsim Y X) (Hxy_Fsim X Y)
  | _ => false

/-! ### Clean Contact-Square Hessian Lemma + Line-Derivative Helpers -/

theorem nonneg_of_hess_pd_square'
    {G Gx Hxx Hxy : ℝ → ℝ → ℝ} {lo hi : ℝ}
    (hr_lo : lo ≤ rStar) (hr_hi : rStar ≤ hi)
    (hG0 : G rStar rStar = 0) (hGx0 : Gx rStar rStar = 0)
    (hderiv_G : ∀ x y s,
      lo ≤ rStar + s * (x - rStar) → rStar + s * (x - rStar) ≤ hi →
      lo ≤ rStar + s * (y - rStar) → rStar + s * (y - rStar) ≤ hi →
      HasDerivAt (fun t => G (rStar + t * (x - rStar)) (rStar + t * (y - rStar)))
        (Gx (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (x - rStar) +
         Gx (rStar + s * (y - rStar)) (rStar + s * (x - rStar)) * (y - rStar)) s)
    (hderiv_dG : ∀ x y s,
      lo ≤ rStar + s * (x - rStar) → rStar + s * (x - rStar) ≤ hi →
      lo ≤ rStar + s * (y - rStar) → rStar + s * (y - rStar) ≤ hi →
      HasDerivAt (fun t => Gx (rStar + t * (x - rStar)) (rStar + t * (y - rStar)) * (x - rStar) +
                           Gx (rStar + t * (y - rStar)) (rStar + t * (x - rStar)) * (y - rStar))
        (Hxx (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (x - rStar) ^ 2 +
         2 * Hxy (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (x - rStar) * (y - rStar) +
         Hxx (rStar + s * (y - rStar)) (rStar + s * (x - rStar)) * (y - rStar) ^ 2) s)
    (hHxy_symm : ∀ u v, Hxy v u = Hxy u v)
    (hpd_sym : ∀ u v, lo ≤ u → u ≤ hi → lo ≤ v → v ≤ hi → u ≤ v →
      ∀ dx dy, 0 ≤ Hxx u v * dx ^ 2 + 2 * Hxy u v * dx * dy + Hxx v u * dy ^ 2)
    {x y : ℝ} (hx_lo : lo ≤ x) (hx_hi : x ≤ hi) (hy_lo : lo ≤ y) (hy_hi : y ≤ hi) :
    0 ≤ G x y := by
  set dx := x - rStar; set dy := y - rStar
  set g : ℝ → ℝ := fun t => G (rStar + t * dx) (rStar + t * dy)
  set g' : ℝ → ℝ := fun t => Gx (rStar + t * dx) (rStar + t * dy) * dx + Gx (rStar + t * dy) (rStar + t * dx) * dy
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      lo ≤ rStar + t * dx ∧ rStar + t * dx ≤ hi ∧ lo ≤ rStar + t * dy ∧ rStar + t * dy ≤ hi := fun t ht => by
    have h1 : rStar + t * dx = (1 - t) * rStar + t * x := by simp only [dx]; ring
    have h2 : rStar + t * dy = (1 - t) * rStar + t * y := by simp only [dy]; ring
    rw [h1, h2]; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [ht.1, ht.2]
  have hg1 : g 1 = G x y := by simp only [g, dx, dy]; ring_nf
  rw [← hg1]
  exact nonneg_of_deriv2_nonneg (a := 0) (b := 1) (r := 0) le_rfl (by norm_num)
    (fun t ht => by have hs := hseg t ht; exact (hderiv_G x y t hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).continuousAt.continuousWithinAt)
    (fun t ht => by have hs := hseg t (Set.Ioo_subset_Icc_self ht); exact hderiv_G x y t hs.1 hs.2.1 hs.2.2.1 hs.2.2.2)
    (fun t ht => by have hs := hseg t ht; exact (hderiv_dG x y t hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).continuousAt.continuousWithinAt)
    (fun t ht => by have hs := hseg t (Set.Ioo_subset_Icc_self ht); exact hderiv_dG x y t hs.1 hs.2.1 hs.2.2.1 hs.2.2.2)
    (fun t ht => by
      have hs := hseg t (Set.Ioo_subset_Icc_self ht)
      set u := rStar + t * dx; set v := rStar + t * dy
      rcases le_total u v with huv | hvu
      · exact hpd_sym u v hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 huv dx dy
      · have := hpd_sym v u hs.2.2.1 hs.2.2.2 hs.1 hs.2.1 hvu dy dx
        rw [hHxy_symm] at this; linarith)
    (by simp [g, hG0])
    (by simp [hGx0])
    1 ⟨by norm_num, le_rfl⟩

/-- Generic line derivative for `t ↦ f(u t) * g(v t) + f(v t) * g(u t)` along `(rStar + t*dx, rStar + t*dy)`. -/
lemma hasDerivAt_symProd_line {f f' g g' : ℝ → ℝ} {x y s : ℝ}
    (hdfu : HasDerivAt f (f' (rStar + s * (x - rStar))) (rStar + s * (x - rStar)))
    (hdfv : HasDerivAt f (f' (rStar + s * (y - rStar))) (rStar + s * (y - rStar)))
    (hdgu : HasDerivAt g (g' (rStar + s * (x - rStar))) (rStar + s * (x - rStar)))
    (hdgv : HasDerivAt g (g' (rStar + s * (y - rStar))) (rStar + s * (y - rStar))) :
    HasDerivAt (fun t => f (rStar + t * (x - rStar)) * g (rStar + t * (y - rStar)) +
                         f (rStar + t * (y - rStar)) * g (rStar + t * (x - rStar)))
      ((f' (rStar + s * (x - rStar)) * g (rStar + s * (y - rStar)) +
        f (rStar + s * (y - rStar)) * g' (rStar + s * (x - rStar))) * (x - rStar) +
       (f' (rStar + s * (y - rStar)) * g (rStar + s * (x - rStar)) +
        f (rStar + s * (x - rStar)) * g' (rStar + s * (y - rStar))) * (y - rStar)) s := by
  set dx := x - rStar; set dy := y - rStar
  set u : ℝ → ℝ := fun t => rStar + t * dx; set v : ℝ → ℝ := fun t => rStar + t * dy
  have hdu : HasDerivAt u dx s := by simpa [u] using ((hasDerivAt_id' s).mul_const dx).const_add rStar
  have hdv : HasDerivAt v dy s := by simpa [v] using ((hasDerivAt_id' s).mul_const dy).const_add rStar
  have hfu := HasDerivAt.comp (h := u) s hdfu hdu
  have hfv := HasDerivAt.comp (h := v) s hdfv hdv
  have hgu := HasDerivAt.comp (h := u) s hdgu hdu
  have hgv := HasDerivAt.comp (h := v) s hdgv hdv
  exact ((hfu.fun_mul hgv).fun_add (hfv.fun_mul hgu)).congr_deriv (by
    simp only [Function.comp_apply, u, v]; ring)

/-- Generic 2nd line derivative for the derivative of `f(u t)*g(v t) + f(v t)*g(u t)`. -/
lemma hasDerivAt_symProd_dline {f f' f'' g g' g'' : ℝ → ℝ} {x y s : ℝ}
    (hdfu : HasDerivAt f (f' (rStar + s * (x - rStar))) (rStar + s * (x - rStar)))
    (hdfv : HasDerivAt f (f' (rStar + s * (y - rStar))) (rStar + s * (y - rStar)))
    (hdfpu : HasDerivAt f' (f'' (rStar + s * (x - rStar))) (rStar + s * (x - rStar)))
    (hdfpv : HasDerivAt f' (f'' (rStar + s * (y - rStar))) (rStar + s * (y - rStar)))
    (hdgu : HasDerivAt g (g' (rStar + s * (x - rStar))) (rStar + s * (x - rStar)))
    (hdgv : HasDerivAt g (g' (rStar + s * (y - rStar))) (rStar + s * (y - rStar)))
    (hdgpu : HasDerivAt g' (g'' (rStar + s * (x - rStar))) (rStar + s * (x - rStar)))
    (hdgpv : HasDerivAt g' (g'' (rStar + s * (y - rStar))) (rStar + s * (y - rStar))) :
    HasDerivAt (fun t =>
        (f' (rStar + t * (x - rStar)) * g (rStar + t * (y - rStar)) +
         f (rStar + t * (y - rStar)) * g' (rStar + t * (x - rStar))) * (x - rStar) +
        (f' (rStar + t * (y - rStar)) * g (rStar + t * (x - rStar)) +
         f (rStar + t * (x - rStar)) * g' (rStar + t * (y - rStar))) * (y - rStar))
      ((f'' (rStar + s * (x - rStar)) * g (rStar + s * (y - rStar)) +
        f (rStar + s * (y - rStar)) * g'' (rStar + s * (x - rStar))) * (x - rStar) ^ 2 +
       2 * (f' (rStar + s * (x - rStar)) * g' (rStar + s * (y - rStar)) +
            f' (rStar + s * (y - rStar)) * g' (rStar + s * (x - rStar))) * (x - rStar) * (y - rStar) +
       (f'' (rStar + s * (y - rStar)) * g (rStar + s * (x - rStar)) +
        f (rStar + s * (x - rStar)) * g'' (rStar + s * (y - rStar))) * (y - rStar) ^ 2) s := by
  set dx := x - rStar; set dy := y - rStar
  set u : ℝ → ℝ := fun t => rStar + t * dx; set v : ℝ → ℝ := fun t => rStar + t * dy
  have hdu : HasDerivAt u dx s := by simpa [u] using ((hasDerivAt_id' s).mul_const dx).const_add rStar
  have hdv : HasDerivAt v dy s := by simpa [v] using ((hasDerivAt_id' s).mul_const dy).const_add rStar
  have hfu := HasDerivAt.comp (h := u) s hdfu hdu
  have hfv := HasDerivAt.comp (h := v) s hdfv hdv
  have hfpu := HasDerivAt.comp (h := u) s hdfpu hdu
  have hfpv := HasDerivAt.comp (h := v) s hdfpv hdv
  have hgu := HasDerivAt.comp (h := u) s hdgu hdu
  have hgv := HasDerivAt.comp (h := v) s hdgv hdv
  have hgpu := HasDerivAt.comp (h := u) s hdgpu hdu
  have hgpv := HasDerivAt.comp (h := v) s hdgpv hdv
  have hd1 := ((hfpu.fun_mul hgv).fun_add (hfv.fun_mul hgpu)).mul_const dx
  have hd2 := ((hfpv.fun_mul hgu).fun_add (hfu.fun_mul hgpv)).mul_const dy
  exact (hd1.fun_add hd2).congr_deriv (by
    simp only [Function.comp_apply, u, v]; ring)

end UCBound.Cert2D
