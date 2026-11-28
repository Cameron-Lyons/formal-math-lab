module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-!
# Basic Definitions, Constants, and Analytic Preliminaries

Defines:
- `UnionClosed`: finite union-closed family of sets
- `h`: binary entropy `h(x) = -x log x - (1 - x) log (1 - x)`
- `L = Real.log 2`
- `rStar`: the unique root in `(0, 1)` of `-(1 - r) log (1 - r) - r log (1 + r) = 0`
- All derived constants (`mStar, qStar, cStar, hr, pStar, cParam, tau, gamma, alpha, t0, bm, DParam, eStar`)
- The kernel functions `I_fun, phi, F_fun, J_fun, R_fun, v_fun, b_fun`
- Analytic properties of `h` and the analytic proof that `J_fun x y ≥ 0` on `[0, 1]²`.
-/

noncomputable section

namespace UCBound

open Real

/-- A finite family of finite sets is union-closed if it is closed under pairwise union. -/
def UnionClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- Natural logarithm of 2. -/
def L : ℝ := Real.log 2

lemma L_pos : 0 < L := Real.log_pos (by norm_num)

/-- Binary entropy function in nats, with convention `0 * log 0 = 0` (already holds in Mathlib
since `Real.log 0 = 0`). -/
def h (x : ℝ) : ℝ := -x * Real.log x - (1 - x) * Real.log (1 - x)

@[simp] lemma h_zero : h 0 = 0 := by simp [h]
@[simp] lemma h_one : h 1 = 0 := by simp [h]

lemma h_half : h (1 / 2) = L := by
  unfold h L
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h1, Real.log_div one_ne_zero (by norm_num), Real.log_one, zero_sub]
  ring

lemma h_symm (x : ℝ) : h (1 - x) = h x := by
  unfold h; ring_nf

lemma h_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ h x := by
  unfold h
  rcases hx0.eq_or_lt with rfl | hx0'
  · simp
  rcases hx1.eq_or_lt with rfl | hx1'
  · simp
  have h1 : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
  have h2 : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  nlinarith

lemma h_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < h x := by
  unfold h
  have h1 : Real.log x < 0 := Real.log_neg hx0 hx1
  have h2 : Real.log (1 - x) < 0 := Real.log_neg (by linarith) (by linarith)
  nlinarith

/-- Derivative of binary entropy on `(0, 1)`: `h'(x) = log ((1 - x) / x)`. -/
def hp (x : ℝ) : ℝ := Real.log ((1 - x) / x)

lemma hasDerivAt_h {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt h (hp x) x := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1x : 1 - x ≠ 0 := ne_of_gt (by linarith)
  have hd1 : HasDerivAt (fun t => -t * Real.log t) (-1 * Real.log x + -x * x⁻¹) x := by
    exact (hasDerivAt_id' x).fun_neg.fun_mul (Real.hasDerivAt_log hxne)
  have hd2 : HasDerivAt (fun t => (1 - t) * Real.log (1 - t))
      ((-1) * Real.log (1 - x) + (1 - x) * ((1 - x)⁻¹ * (-1))) x := by
    have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x)
    have hlog : HasDerivAt (fun t : ℝ => Real.log (1 - t)) ((1 - x)⁻¹ * (-1)) x :=
      (Real.hasDerivAt_log h1x).comp x hsub
    exact hsub.fun_mul hlog
  have hdiff : HasDerivAt h
      ((-1 * Real.log x + -x * x⁻¹) - ((-1) * Real.log (1 - x) + (1 - x) * ((1 - x)⁻¹ * (-1)))) x :=
    hd1.fun_sub hd2
  convert hdiff using 1
  unfold hp
  rw [Real.log_div h1x hxne]
  field_simp [hxne, h1x]
  ring

lemma hasDerivAt_hp {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt hp (-(1 / (x * (1 - x)))) x := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1x : 1 - x ≠ 0 := ne_of_gt (by linarith)
  have hquot : HasDerivAt (fun t => (1 - t) / t) (((-1) * x - (1 - x) * 1) / x ^ 2) x := by
    have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x)
    exact hsub.fun_div (hasDerivAt_id' x) hxne
  have hpos : (1 - x) / x ≠ 0 := div_ne_zero h1x hxne
  have hcomp := hquot.log hpos
  exact hcomp.congr_deriv (by field_simp [hxne, h1x]; ring)

lemma continuousOn_h : ContinuousOn h (Set.Icc 0 1) := by
  unfold h
  have h1 : Continuous (fun x : ℝ => -x * Real.log x) := by
    have hc : Continuous (fun x : ℝ => -(x * Real.log x)) := Real.continuous_mul_log.neg
    convert hc using 1; ext x; ring
  have h2 : Continuous (fun x : ℝ => (1 - x) * Real.log (1 - x)) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  exact (h1.sub h2).continuousOn

lemma concaveOn_h : ConcaveOn ℝ (Set.Icc 0 1) h := by
  apply concaveOn_of_deriv2_nonpos (convex_Icc 0 1) continuousOn_h
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_h hx.1 hx.2).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hderiv_eq : deriv h =ᶠ[nhds x] hp := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact (hasDerivAt_h hy.1 hy.2).deriv
    exact ((hasDerivAt_hp hx.1 hx.2).congr_of_eventuallyEq hderiv_eq).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hderiv_eq : deriv h =ᶠ[nhds x] hp := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact (hasDerivAt_h hy.1 hy.2).deriv
    have h2 : deriv (deriv h) x = -(1 / (x * (1 - x))) :=
      ((hasDerivAt_hp hx.1 hx.2).congr_of_eventuallyEq hderiv_eq).deriv
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rw [h2]
    have hpos : 0 < x * (1 - x) := mul_pos hx.1 (by linarith [hx.2])
    linarith [one_div_pos.mpr hpos]

lemma h_le_L {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : h x ≤ L := by
  have hconc := concaveOn_h.2 (show x ∈ Set.Icc 0 1 from ⟨hx0, hx1⟩)
    (show 1 - x ∈ Set.Icc 0 1 from ⟨by linarith, by linarith⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (1 - x) = 1 / 2 := by ring
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hmid, h_half, h_symm] at hconc
  linarith

/-- The stationary equation `rootEq(x) = -(1 - x) log (1 - x) - x log (1 + x)` defining `rStar`. -/
def rootEq (x : ℝ) : ℝ := -(1 - x) * Real.log (1 - x) - x * Real.log (1 + x)

lemma hasDerivAt_rootEq {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    HasDerivAt rootEq (Real.log ((1 - x) / (1 + x)) + 1 / (1 + x)) x := by
  have h1mx : 1 - x ≠ 0 := ne_of_gt (by linarith)
  have h1px : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hd1 : HasDerivAt (fun t => -(1 - t) * Real.log (1 - t))
      (1 * Real.log (1 - x) + -(1 - x) * ((1 - x)⁻¹ * (-1))) x := by
    have ha : HasDerivAt (fun t : ℝ => -(1 - t)) 1 x := by
      have : (fun t : ℝ => -(1 - t)) = (fun t : ℝ => t - 1) := by ext t; ring
      rw [this]; simpa using (hasDerivAt_id' x).fun_sub (hasDerivAt_const x (1 : ℝ))
    have hb : HasDerivAt (fun t : ℝ => Real.log (1 - t)) ((1 - x)⁻¹ * (-1)) x :=
      (Real.hasDerivAt_log h1mx).comp x (by simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x))
    exact ha.fun_mul hb
  have hd2 : HasDerivAt (fun t => t * Real.log (1 + t))
      (1 * Real.log (1 + x) + x * ((1 + x)⁻¹ * 1)) x := by
    have hb : HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + x)⁻¹ * 1) x :=
      (Real.hasDerivAt_log h1px).comp x (by simpa using (hasDerivAt_const x (1 : ℝ)).fun_add (hasDerivAt_id' x))
    exact (hasDerivAt_id' x).fun_mul hb
  have hdiff : HasDerivAt rootEq
      ((1 * Real.log (1 - x) + -(1 - x) * ((1 - x)⁻¹ * (-1))) - (1 * Real.log (1 + x) + x * ((1 + x)⁻¹ * 1))) x :=
    hd1.fun_sub hd2
  convert hdiff using 1
  rw [Real.log_div h1mx h1px]
  field_simp [h1mx, h1px]
  ring

lemma hasDerivAt_rootEq' {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    HasDerivAt (fun t => Real.log ((1 - t) / (1 + t)) + 1 / (1 + t))
      (-(1 / (1 - x)) - 1 / (1 + x) - 1 / (1 + x) ^ 2) x := by
  have h1mx : 1 - x ≠ 0 := ne_of_gt (by linarith)
  have h1px : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hd_log1 : HasDerivAt (fun t => Real.log (1 - t)) ((1 - x)⁻¹ * (-1)) x :=
    (Real.hasDerivAt_log h1mx).comp x (by simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x))
  have hd_log2 : HasDerivAt (fun t => Real.log (1 + t)) ((1 + x)⁻¹ * 1) x :=
    (Real.hasDerivAt_log h1px).comp x (by simpa using (hasDerivAt_const x (1 : ℝ)).fun_add (hasDerivAt_id' x))
  have hd_inv : HasDerivAt (fun t => 1 / (1 + t)) (-(1 / (1 + x) ^ 2)) x := by
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_add (hasDerivAt_id' x)
    have h2 := h1.inv h1px
    convert h2 using 1
    · ext t; simp [one_div]
    · ring
  have hsum := (hd_log1.fun_sub hd_log2).fun_add hd_inv
  have heq : (fun t => Real.log (1 - t) - Real.log (1 + t) + 1 / (1 + t)) =ᶠ[nhds x]
      (fun t => Real.log ((1 - t) / (1 + t)) + 1 / (1 + t)) := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with t ht
    rw [Real.log_div (ne_of_gt (by linarith [ht.2])) (ne_of_gt (by linarith [ht.1]))]
  convert hsum.congr_of_eventuallyEq heq.symm using 1
  ring

lemma rootEq_continuousOn : ContinuousOn rootEq (Set.Icc 0 1) := by
  unfold rootEq
  have h1 : Continuous (fun x : ℝ => -(1 - x) * Real.log (1 - x)) := by
    have hc : Continuous (fun x : ℝ => -((1 - x) * Real.log (1 - x))) :=
      (Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).neg
    convert hc using 1; ext x; ring
  have h2 : ContinuousOn (fun x : ℝ => x * Real.log (1 + x)) (Set.Icc 0 1) := by
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.log (continuousOn_const.add continuousOn_id)
    intro x hx; exact ne_of_gt (show (0 : ℝ) < 1 + x by linarith [hx.1])
  exact h1.continuousOn.sub h2

lemma rootEq_half_pos : 0 < rootEq (1 / 2) := by
  unfold rootEq
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have h2 : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [h1, h2, Real.log_div one_ne_zero (by norm_num), Real.log_one, zero_sub,
      Real.log_div (by norm_num) (by norm_num)]
  have hlog : Real.log 3 < 2 * Real.log 2 := by
    have : Real.log 3 < Real.log (2 ^ 2) := Real.log_lt_log (by norm_num) (by norm_num)
    simpa [Real.log_pow] using this
  linarith

lemma rootEq_one_neg : rootEq 1 < 0 := by
  unfold rootEq
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 : ℝ) + 1 = 2 := by norm_num
  simp [h1, h2]

lemma rootEq_strictAntiOn_half_one : StrictAntiOn rootEq (Set.Icc (1 / 2) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (1 / 2) 1)
  · exact rootEq_continuousOn.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
  · intro x hx
    rw [interior_Icc] at hx
    have hd := hasDerivAt_rootEq (by linarith [hx.1]) hx.2
    rw [hd.deriv]
    -- Show log((1-x)/(1+x)) + 1/(1+x) < 0 for x > 1/2
    -- Since f'(x) is strictly decreasing on (1/2, 1) and f'(1/2) = log(1/3) + 2/3 < 0
    -- Actually simpler: for x ∈ (1/2, 1), let u = (1-x)/(1+x) ∈ (0, 1/3).
    -- log u + (1+u)/2 < 0 since for u ∈ (0, 1/3), log u ≤ log(1/3) = -log 3 < -1, while (1+u)/2 < 2/3!
    have h1px : 0 < 1 + x := by linarith [hx.1]
    have h1mx : 0 < 1 - x := by linarith [hx.2]
    have hu_le : (1 - x) / (1 + x) < 1 / 3 := by
      rw [div_lt_div_iff₀ h1px (by norm_num)]
      linarith [hx.1]
    have hlog_u : Real.log ((1 - x) / (1 + x)) < Real.log (1 / 3) :=
      Real.log_lt_log (div_pos h1mx h1px) hu_le
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      simpa using this
    have hlog13 : Real.log (1 / 3 : ℝ) < -1 := by
      rw [Real.log_div one_ne_zero (by norm_num), Real.log_one]; linarith
    have hinv : 1 / (1 + x) < 2 / 3 := by
      rw [div_lt_div_iff₀ h1px (by norm_num)]; linarith [hx.1]
    linarith

/-- Existence and uniqueness of `rStar` in `[1/2, 1]` satisfying `rootEq rStar = 0`. -/
lemma existsUnique_rStar : ∃! x ∈ Set.Ioo (1 / 2 : ℝ) 1, rootEq x = 0 := by
  have hcont : ContinuousOn rootEq (Set.Icc (1 / 2) 1) :=
    rootEq_continuousOn.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
  have h0 : (0 : ℝ) ∈ Set.Icc (rootEq 1) (rootEq (1 / 2)) :=
    ⟨le_of_lt rootEq_one_neg, le_of_lt rootEq_half_pos⟩
  obtain ⟨r, hr_mem, hr_eq⟩ := intermediate_value_Icc' (by norm_num) hcont h0
  have hr_oo : r ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne hr_mem.1 ?_, lt_of_le_of_ne hr_mem.2 ?_⟩
    · intro h; subst h; linarith [rootEq_half_pos]
    · intro h; subst h; linarith [rootEq_one_neg]
  refine ⟨r, ⟨hr_oo, hr_eq⟩, ?_⟩
  intro y ⟨hy_oo, hy_eq⟩
  exact rootEq_strictAntiOn_half_one.injOn (Set.Ioo_subset_Icc_self hy_oo)
    (Set.Ioo_subset_Icc_self hr_oo) (hy_eq.trans hr_eq.symm)

/-- The canonical contact point `rStar ≈ 0.69090773872540775` in `(1/2, 1)`. -/
def rStar : ℝ := Classical.choose existsUnique_rStar

lemma rStar_mem_Ioo : rStar ∈ Set.Ioo (1 / 2 : ℝ) 1 :=
  (Classical.choose_spec existsUnique_rStar).1.1

lemma rStar_pos : 0 < rStar := by linarith [rStar_mem_Ioo.1]
lemma rStar_lt_one : rStar < 1 := rStar_mem_Ioo.2
lemma rStar_gt_half : 1 / 2 < rStar := rStar_mem_Ioo.1

lemma rootEq_rStar : rootEq rStar = 0 :=
  (Classical.choose_spec existsUnique_rStar).1.2

lemma rStar_eq_of_rootEq {x : ℝ} (hx : x ∈ Set.Ioo (1 / 2 : ℝ) 1) (h0 : rootEq x = 0) :
    x = rStar :=
  (Classical.choose_spec existsUnique_rStar).2 x ⟨hx, h0⟩

lemma lt_rStar_of_rootEq_pos {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) (hpos : 0 < rootEq x) :
    x < rStar := by
  by_contra hle
  push Not at hle
  rcases hle.eq_or_lt with rfl | hlt
  · linarith [rootEq_rStar]
  · have := rootEq_strictAntiOn_half_one (Set.Ioo_subset_Icc_self rStar_mem_Ioo) hx hlt
    linarith [rootEq_rStar]

lemma rStar_lt_of_rootEq_neg {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) (hneg : rootEq x < 0) :
    rStar < x := by
  by_contra hle
  push Not at hle
  rcases hle.eq_or_lt with rfl | hlt
  · linarith [rootEq_rStar]
  · have := rootEq_strictAntiOn_half_one hx (Set.Ioo_subset_Icc_self rStar_mem_Ioo) hlt
    linarith [rootEq_rStar]

/-! ### Derived Constants -/

def mStar : ℝ := 1 / 2 + (1 - rStar) * Real.log (1 + rStar) / (2 * L)
def qStar : ℝ := 2 * mStar - 1
def cStar : ℝ := 1 - mStar
def hr : ℝ := h rStar
def pStar : ℝ := hp rStar
def cParam : ℝ := rStar - hr / pStar
def tau : ℝ := (1 / 2 - rStar ^ 2) / (rStar ^ 2 * (1 - rStar) ^ 2)
def gamma : ℝ := hr / rStar
def alpha : ℝ := 1 - gamma / pStar
def t0 : ℝ := rStar - mStar
def bm : ℝ := -hr * gamma / (pStar * alpha)
def DParam : ℝ := -hr / (pStar * alpha) - t0
def eStar : ℝ := gamma * mStar

lemma qStar_add_one : qStar + 1 = 2 * mStar := by unfold qStar; ring
lemma cStar_add_mStar : cStar + mStar = 1 := by unfold cStar; ring

lemma hr_pos : 0 < hr := h_pos rStar_pos rStar_lt_one

lemma pStar_neg : pStar < 0 := by
  unfold pStar hp
  have h1 : (1 - rStar) / rStar < 1 := by
    rw [div_lt_one rStar_pos]; linarith [rStar_gt_half]
  exact Real.log_neg (div_pos (by linarith [rStar_lt_one]) rStar_pos) h1

lemma pStar_ne_zero : pStar ≠ 0 := ne_of_lt pStar_neg

lemma gamma_pos : 0 < gamma := div_pos hr_pos rStar_pos

lemma alpha_pos : 0 < alpha := by
  unfold alpha
  have hdiv : gamma / pStar < 0 := div_neg_of_pos_of_neg gamma_pos pStar_neg
  linarith

lemma cParam_eq_rStar_mul_alpha : cParam = rStar * alpha := by
  unfold cParam alpha gamma
  have hr0 : rStar ≠ 0 := ne_of_gt rStar_pos
  field_simp [hr0, pStar_ne_zero]

lemma cParam_pos : 0 < cParam := by
  rw [cParam_eq_rStar_mul_alpha]; exact mul_pos rStar_pos alpha_pos

lemma bm_pos : 0 < bm := by
  unfold bm
  have hden : pStar * alpha < 0 := mul_neg_of_neg_of_pos pStar_neg alpha_pos
  exact div_pos_of_neg_of_neg (by nlinarith [hr_pos, gamma_pos]) hden

/-- Exact contact identity: `h(rStar^2) + qStar * L = 2 * rStar * hr`. -/
lemma contact_identity : h (rStar ^ 2) + qStar * L = 2 * rStar * hr := by
  have hr0 : 0 < rStar := rStar_pos
  have hr1 : rStar < 1 := rStar_lt_one
  have h1mr : 0 < 1 - rStar := by linarith
  have h1pr : 0 < 1 + rStar := by linarith
  have h1mr2 : 1 - rStar ^ 2 = (1 - rStar) * (1 + rStar) := by ring
  have hroot : (1 - rStar) * Real.log (1 - rStar) = -rStar * Real.log (1 + rStar) := by
    have := rootEq_rStar
    unfold rootEq at this
    linarith
  have hqL : qStar * L = (1 - rStar) * Real.log (1 + rStar) := by
    unfold qStar mStar
    have hL : L ≠ 0 := ne_of_gt L_pos
    field_simp [hL]
    ring
  rw [hqL]
  unfold hr h
  rw [Real.log_pow, h1mr2, Real.log_mul (ne_of_gt h1mr) (ne_of_gt h1pr)]
  push_cast
  -- Goal: -r^2*(2*log r) - (1-r)*(1+r)*(log(1-r)+log(1+r)) + (1-r)*log(1+r)
  --     = 2*r*(-r*log r - (1-r)*log(1-r))
  -- Expand and substitute (1-r)*log(1-r) = -r*log(1+r)!
  have hkey : (1 - rStar) * (1 + rStar) * (Real.log (1 - rStar) + Real.log (1 + rStar))
      = (1 + rStar) * ((1 - rStar) * Real.log (1 - rStar))
        + (1 - rStar) * (1 + rStar) * Real.log (1 + rStar) := by ring
  rw [hkey, hroot]
  have hkey2 : 2 * rStar * ((1 - rStar) * Real.log (1 - rStar)) =
      2 * rStar * (-rStar * Real.log (1 + rStar)) := by rw [hroot]
  linarith [hkey2]

lemma qStar_pos : 0 < qStar := by
  have hqL : qStar * L = (1 - rStar) * Real.log (1 + rStar) := by
    unfold qStar mStar
    have hL : L ≠ 0 := ne_of_gt L_pos
    field_simp [hL]; ring
  have hpos : 0 < (1 - rStar) * Real.log (1 + rStar) :=
    mul_pos (by linarith [rStar_lt_one]) (Real.log_pos (by linarith [rStar_pos]))
  nlinarith [L_pos]

lemma mStar_gt_half : 1 / 2 < mStar := by
  have hq := qStar_pos
  unfold qStar at hq
  linarith

/-! ### Kernel Functions -/

/-- Conditionally i.i.d. product kernel `I(x, y) = x y (1 + τ (1 - x) (1 - y))`. -/
def I_fun (x y : ℝ) : ℝ := x * y * (1 + tau * (1 - x) * (1 - y))

/-- Rank-1 profile `φ(x) = √(h(I(x, x)) / L)`. -/
def phi (x : ℝ) : ℝ := Real.sqrt (h (I_fun x x) / L)

/-- Independent-plus-rank-1 excess `F(x, y) = h(xy) + qL φ(x)φ(y) - y h(x) - x h(y)`. -/
def F_fun (x y : ℝ) : ℝ := h (x * y) + qStar * L * phi x * phi y - y * h x - x * h y

/-- CIID kernel excess `J(x, y) = h(I(x, y)) - L φ(x) φ(y)`. -/
def J_fun (x y : ℝ) : ℝ := h (I_fun x y) - L * phi x * phi y

/-- Single-coordinate residual `R(x) = F(rStar, x) / (qStar * L)`. -/
def R_fun (x : ℝ) : ℝ := F_fun rStar x / (qStar * L)

/-- Entropy-profile difference `v(x) = h(x) - h(rStar) φ(x)`. -/
def v_fun (x : ℝ) : ℝ := h x - hr * phi x

/-- Mean-entropy-profile residual `b(x) = x - h(x) / pStar - cParam * φ(x)`. -/
def b_fun (x : ℝ) : ℝ := x - h x / pStar - cParam * phi x

@[simp] lemma I_fun_zero_left (y : ℝ) : I_fun 0 y = 0 := by simp [I_fun]
@[simp] lemma I_fun_zero_right (x : ℝ) : I_fun x 0 = 0 := by simp [I_fun]
@[simp] lemma I_fun_one_left (y : ℝ) : I_fun 1 y = y := by simp [I_fun]
@[simp] lemma I_fun_one_right (x : ℝ) : I_fun x 1 = x := by simp [I_fun]
lemma I_fun_symm (x y : ℝ) : I_fun x y = I_fun y x := by unfold I_fun; ring

lemma I_fun_rStar_rStar : I_fun rStar rStar = 1 / 2 := by
  unfold I_fun tau
  have hr0 : rStar ≠ 0 := ne_of_gt rStar_pos
  have h1r : 1 - rStar ≠ 0 := ne_of_gt (by linarith [rStar_lt_one])
  field_simp [hr0, h1r]
  ring

@[simp] lemma phi_zero : phi 0 = 0 := by simp [phi]
@[simp] lemma phi_one : phi 1 = 0 := by simp [phi]

lemma phi_rStar : phi rStar = 1 := by
  unfold phi
  rw [I_fun_rStar_rStar, h_half, div_self (ne_of_gt L_pos), Real.sqrt_one]

lemma phi_nonneg (x : ℝ) : 0 ≤ phi x := Real.sqrt_nonneg _

lemma I_fun_mem_Icc {x y : ℝ} (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ I_fun x y ∧ I_fun x y ≤ 1 := by
  unfold I_fun
  constructor
  · apply mul_nonneg (mul_nonneg hx0 hy0)
    have : 0 ≤ tau * (1 - x) * (1 - y) := mul_nonneg (mul_nonneg htau0 (by linarith)) (by linarith)
    linarith
  · have h1 : tau * (1 - x) * (1 - y) ≤ (1 - x) * (1 - y) := by
      have hnn : 0 ≤ (1 - x) * (1 - y) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have h2 : x * y * (1 + (1 - x) * (1 - y)) ≤ 1 := by
      have hid : 1 - x * y * (1 + (1 - x) * (1 - y))
          = (1 - x) * (1 - y) * (1 - x * y) + x * (1 - y) + y * (1 - x) := by ring
      have h3 : 0 ≤ (1 - x) * (1 - y) * (1 - x * y) := by
        apply mul_nonneg (mul_nonneg (by linarith) (by linarith))
        nlinarith
      have h4 : 0 ≤ x * (1 - y) := mul_nonneg hx0 (by linarith)
      have h5 : 0 ≤ y * (1 - x) := mul_nonneg hy0 (by linarith)
      linarith
    nlinarith [mul_nonneg hx0 hy0]

lemma phi_le_one {x : ℝ} (htau0 : 0 ≤ tau) (htau1 : tau ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    phi x ≤ 1 := by
  unfold phi
  have hI := I_fun_mem_Icc htau0 htau1 hx0 hx1 hx0 hx1
  have hh : h (I_fun x x) ≤ L := h_le_L hI.1 hI.2
  have hdiv : h (I_fun x x) / L ≤ 1 := (div_le_one L_pos).mpr hh
  calc Real.sqrt (h (I_fun x x) / L) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hdiv
    _ = 1 := Real.sqrt_one

lemma F_fun_symm (x y : ℝ) : F_fun x y = F_fun y x := by unfold F_fun; ring
lemma J_fun_symm (x y : ℝ) : J_fun x y = J_fun y x := by unfold J_fun; rw [I_fun_symm]; ring

@[simp] lemma R_fun_zero : R_fun 0 = 0 := by simp [R_fun, F_fun]
@[simp] lemma R_fun_one : R_fun 1 = 0 := by simp [R_fun, F_fun]
@[simp] lemma R_fun_rStar : R_fun rStar = 0 := by
  unfold R_fun F_fun
  rw [phi_rStar, mul_one, mul_one]
  have hc := contact_identity
  unfold hr at hc
  have hsq : rStar * rStar = rStar ^ 2 := by ring
  rw [hsq]
  have hnum : h (rStar ^ 2) + qStar * L - rStar * h rStar - rStar * h rStar = 0 := by linarith
  rw [hnum, zero_div]

lemma R_fun_eq (x : ℝ) : R_fun x = phi x + (h (rStar * x) - rStar * h x - x * hr) / (qStar * L) := by
  unfold R_fun F_fun hr
  rw [phi_rStar]
  have hq : qStar ≠ 0 := ne_of_gt qStar_pos
  have hL : L ≠ 0 := ne_of_gt L_pos
  field_simp [hq, hL]
  ring

@[simp] lemma v_fun_zero : v_fun 0 = 0 := by simp [v_fun]
@[simp] lemma v_fun_one : v_fun 1 = 0 := by simp [v_fun]
@[simp] lemma v_fun_rStar : v_fun rStar = 0 := by simp [v_fun, phi_rStar, hr]

@[simp] lemma b_fun_zero : b_fun 0 = 0 := by simp [b_fun]
@[simp] lemma b_fun_one : b_fun 1 = 1 := by simp [b_fun]
@[simp] lemma b_fun_rStar : b_fun rStar = 0 := by
  unfold b_fun cParam hr; rw [phi_rStar]; ring

/-- Key algebraic identity connecting `(x - mStar) h(x)` to `DParam, bm, b_fun, R_fun`. -/
lemma signed_pointwise_identity (x : ℝ) :
    (x - mStar) * h x + DParam * h x - bm * x + bm * b_fun x
      = (x - rStar) * h x - (hr / pStar) * v_fun x := by
  unfold DParam bm b_fun v_fun t0 cParam
  have hp0 : pStar ≠ 0 := pStar_ne_zero
  have ha0 : alpha ≠ 0 := ne_of_gt alpha_pos
  have halpha : alpha = 1 - gamma / pStar := rfl
  have hgamma : gamma = hr / rStar := rfl
  have hr0 : rStar ≠ 0 := ne_of_gt rStar_pos
  have hlin : pStar * alpha = pStar - hr / rStar := by
    rw [halpha, hgamma]; field_simp [hp0, hr0]
  field_simp [hp0, ha0]
  rw [halpha, hgamma]
  field_simp [hp0, hr0]
  ring

/-- Key identity `bm * mStar - DParam * eStar = t0 * eStar`. -/
lemma bm_mStar_sub_DParam_eStar : bm * mStar - DParam * eStar = t0 * eStar := by
  unfold bm DParam eStar gamma
  have hp0 : pStar ≠ 0 := pStar_ne_zero
  have ha0 : alpha ≠ 0 := ne_of_gt alpha_pos
  have hr0 : rStar ≠ 0 := ne_of_gt rStar_pos
  field_simp [hp0, ha0, hr0]
  ring

/-- Exact identity `h(x) - gamma * x = alpha * v_fun x - gamma * b_fun x`. -/
lemma linear_v_b_identity (x : ℝ) :
    h x - gamma * x = alpha * v_fun x - gamma * b_fun x := by
  unfold v_fun b_fun cParam alpha gamma
  have hp0 : pStar ≠ 0 := pStar_ne_zero
  have hr0 : rStar ≠ 0 := ne_of_gt rStar_pos
  field_simp [hp0, hr0]
  ring

/-! ### Analytic Proof of `J_fun x y ≥ 0` (Lemma 2.1 of Sadhu–Ursin) -/

/-- Auxiliary: `u * exp(-u) ≤ exp(-1)` for all `u : ℝ`. -/
lemma mul_exp_neg_le (u : ℝ) : u * Real.exp (-u) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (u - 1)
  -- u ≤ exp(u - 1) = exp(u) * exp(-1)
  have h1 : u ≤ Real.exp (u - 1) := by linarith
  have h2 : u * Real.exp (-u) ≤ Real.exp (u - 1) * Real.exp (-u) :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
  rw [← Real.exp_add] at h2
  have h3 : u - 1 + -u = -1 := by ring
  rwa [h3] at h2

/-- Auxiliary: `u^2 * exp(-u) ≤ 4 * exp(-2)` for all `u ≥ 0`. -/
lemma sq_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) : u ^ 2 * Real.exp (-u) ≤ 4 * Real.exp (-2) := by
  have h := mul_exp_neg_le (u / 2)
  have hnn : 0 ≤ u / 2 * Real.exp (-(u / 2)) := mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
  have hsq : (u / 2 * Real.exp (-(u / 2))) ^ 2 ≤ (Real.exp (-1)) ^ 2 :=
    sq_le_sq' (by linarith [Real.exp_pos (-1)]) h
  have hl : (u / 2 * Real.exp (-(u / 2))) ^ 2 = (u ^ 2 / 4) * Real.exp (-u) := by
    rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hr2 : (Real.exp (-1)) ^ 2 = Real.exp (-2) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [hl, hr2] at hsq
  linarith

/-- Auxiliary: `4 * exp(-2) + exp(-1) < 1`. -/
lemma four_exp_neg_two_add_exp_neg_one_lt_one : 4 * Real.exp (-2) + Real.exp (-1) < 1 := by
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he1 : Real.exp (-1) < 1 / 2.718 := by
    rw [Real.exp_neg, one_div]
    exact inv_strictAnti₀ (by norm_num) he
  have he2 : Real.exp (-2) < 1 / 2.718 ^ 2 := by
    have hsq : Real.exp (-2) = (Real.exp (-1)) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have he1' : Real.exp (-1) < (2.718 : ℝ)⁻¹ := by simpa [one_div] using he1
    rw [hsq, one_div, ← inv_pow]
    exact pow_lt_pow_left₀ he1' (le_of_lt (Real.exp_pos _)) (by norm_num)
  linarith

/-- Key curvature inequality `(2.5)` for `a(t) = log h(t)` on `(0, 1/2)`:
    `-t * a''(t) ≥ (1 + t) * a'(t)`. -/
lemma log_h_curv {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (1 + t) * (hp t / h t) ≤
      t * ((1 / (t * (1 - t)) * h t + (hp t) ^ 2) / (h t) ^ 2) := by
  have hht : 0 < h t := h_pos ht0 (by linarith)
  have h1mt : 0 < 1 - t := by linarith
  have hpos_den : 0 < (h t) ^ 2 := sq_pos_of_pos hht
  -- Multiply both sides by (h t)^2 / t > 0:
  rw [← sub_nonneg]
  have hrew : t * ((1 / (t * (1 - t)) * h t + (hp t) ^ 2) / (h t) ^ 2) - (1 + t) * (hp t / h t)
      = (t / (h t) ^ 2) * (hp t / (1 - t) - t * (hp t) ^ 2
          + (-Real.log (1 - t)) / t * (1 / (1 - t) - (1 + t) * hp t)) := by
    have hh_id : h t = t * hp t + (-Real.log (1 - t)) := by
      unfold h hp
      rw [Real.log_div (ne_of_gt h1mt) (ne_of_gt ht0)]
      ring
    have hht0 : h t ≠ 0 := ne_of_gt hht
    have htne : t ≠ 0 := ne_of_gt ht0
    have h1ne : 1 - t ≠ 0 := ne_of_gt h1mt
    rw [hh_id]
    field_simp [hht0, htne, h1ne]
    ring
  rw [hrew]
  apply mul_nonneg (div_nonneg (le_of_lt ht0) (le_of_lt hpos_den))
  set w := hp t
  set ell := -Real.log (1 - t)
  have hw_pos : 0 < w := by
    unfold w hp
    apply Real.log_pos
    rw [one_lt_div ht0]; linarith
  have hw_lt : w < Real.log (1 / t) := by
    unfold w hp
    apply Real.log_lt_log (div_pos h1mt ht0)
    rw [div_lt_div_iff₀ ht0 ht0]; nlinarith
  have hell_ge : 1 ≤ ell / t := by
    rw [le_div_iff₀ ht0, one_mul]
    have := Real.log_le_sub_one_of_pos h1mt
    linarith
  have hell_le : ell / t ≤ 1 / (1 - t) := by
    rw [div_le_div_iff₀ ht0 h1mt, one_mul]
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1mt)
    rw [Real.log_inv] at this
    have h1 : (1 - t)⁻¹ - 1 = t / (1 - t) := by field_simp [ne_of_gt h1mt]; ring
    rw [h1] at this
    have h2 := (le_div_iff₀ h1mt).mp (show ell ≤ t / (1 - t) by exact this)
    linarith
  -- Bounds on t * w^2 and t * w / (1 - t):
  have hu_pos : 0 ≤ Real.log (1 / t) := le_of_lt (Real.log_pos (by rw [one_lt_div ht0]; linarith))
  have htw2 : t * w ^ 2 ≤ 4 * Real.exp (-2) := by
    have h1 : w ^ 2 ≤ (Real.log (1 / t)) ^ 2 :=
      sq_le_sq' (by linarith) (le_of_lt hw_lt)
    have h2 : t = Real.exp (-Real.log (1 / t)) := by
      rw [Real.exp_neg, Real.exp_log (div_pos one_pos ht0), one_div, inv_inv]
    calc t * w ^ 2 ≤ t * (Real.log (1 / t)) ^ 2 := mul_le_mul_of_nonneg_left h1 (le_of_lt ht0)
      _ = (Real.log (1 / t)) ^ 2 * Real.exp (-Real.log (1 / t)) := by rw [← h2]; ring
      _ ≤ 4 * Real.exp (-2) := sq_mul_exp_neg_le hu_pos
  have htw_frac : t * w / (1 - t) ≤ Real.exp (-1) := by
    have h1 : t / (1 - t) = Real.exp (-w) := by
      unfold w hp
      rw [Real.exp_neg, Real.exp_log (div_pos h1mt ht0), inv_div]
    calc t * w / (1 - t) = w * (t / (1 - t)) := by ring
      _ = w * Real.exp (-w) := by rw [h1]
      _ ≤ Real.exp (-1) := mul_exp_neg_le w
  have hexp_lt : 4 * Real.exp (-2) + Real.exp (-1) < 1 := four_exp_neg_two_add_exp_neg_one_lt_one
  have h1_le_inv : 1 ≤ 1 / (1 - t) := by rw [le_div_iff₀ h1mt]; linarith
  by_cases hsign : 0 ≤ 1 / (1 - t) - (1 + t) * w
  · have hstep : 1 * (1 / (1 - t) - (1 + t) * w) ≤ ell / t * (1 / (1 - t) - (1 + t) * w) :=
      mul_le_mul_of_nonneg_right hell_ge hsign
    -- w/(1-t) - t*w^2 + 1/(1-t) - (1+t)*w = 1/(1-t) - t*w^2 + w*(1/(1-t) - 1 - t)
    -- Wait: 1/(1-t) - 1 - t = t^2/(1-t) ≥ 0!
    have hcoeff : 0 ≤ 1 / (1 - t) - (1 + t) := by
      have : 1 / (1 - t) - (1 + t) = t ^ 2 / (1 - t) := by field_simp [ne_of_gt h1mt]; ring
      rw [this]; positivity
    have hmul : 0 ≤ w * (1 / (1 - t) - (1 + t)) := mul_nonneg (le_of_lt hw_pos) hcoeff
    have heq : w / (1 - t) - t * w ^ 2 + 1 * (1 / (1 - t) - (1 + t) * w)
        = (1 / (1 - t) - t * w ^ 2) + w * (1 / (1 - t) - (1 + t)) := by ring
    linarith [Real.exp_pos (-1)]
  · push Not at hsign
    have hstep : 1 / (1 - t) * (1 / (1 - t) - (1 + t) * w)
        ≤ ell / t * (1 / (1 - t) - (1 + t) * w) :=
      mul_le_mul_of_nonpos_right hell_le (le_of_lt hsign)
    have hsimp : w / (1 - t) - t * w ^ 2 + 1 / (1 - t) * (1 / (1 - t) - (1 + t) * w)
        = (1 / (1 - t)) ^ 2 - t * w ^ 2 - t * w / (1 - t) := by ring
    have hsq1 : (1 : ℝ) ≤ (1 / (1 - t)) ^ 2 := by nlinarith
    linarith

/-- Analytic proof of Lemma 2.1: `J_fun x y ≥ 0` for all `x, y ∈ [0, 1]`,
    assuming `0 < tau` and `tau < 1 / 2`. -/
lemma J_fun_nonneg_of_tau {x y : ℝ} (htau0 : 0 < tau) (htau1 : tau < 1 / 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ J_fun x y := by
  -- Boundary cases x=0, y=0, x=1, y=1 are immediate!
  rcases hx0.eq_or_lt with rfl | hx0'
  · simp [J_fun]
  rcases hy0.eq_or_lt with rfl | hy0'
  · simp [J_fun]
  rcases hx1.eq_or_lt with rfl | hx1'
  · unfold J_fun; simp [phi_one, h_nonneg (le_of_lt hy0') hy1]
  rcases hy1.eq_or_lt with rfl | hy1'
  · unfold J_fun; simp [phi_one, h_nonneg (le_of_lt hx0') hx1]
  -- Interior case: x, y ∈ (0, 1). By symmetry assume x ≤ y (if x = y, J_fun x x = 0).
  suffices hmain : ∀ u v : ℝ, 0 < u → u ≤ v → v < 1 → 0 ≤ J_fun u v by
    rcases le_total x y with hxy | hyx
    · exact hmain x y hx0' hxy hy1'
    · rw [J_fun_symm]; exact hmain y x hy0' hyx hx1'
  intro u v hu0 huv hv1
  rcases huv.eq_or_lt with rfl | huv'
  · unfold J_fun phi
    have hI := I_fun_mem_Icc (le_of_lt htau0) (by linarith) (le_of_lt hu0) (le_of_lt hv1)
        (le_of_lt hu0) (le_of_lt hv1)
    have hh : 0 ≤ h (I_fun u u) := h_nonneg hI.1 hI.2
    have hsq : Real.sqrt (h (I_fun u u) / L) * Real.sqrt (h (I_fun u u) / L) = h (I_fun u u) / L :=
      Real.mul_self_sqrt (div_nonneg hh (le_of_lt L_pos))
    have hL : L ≠ 0 := ne_of_gt L_pos
    have : L * Real.sqrt (h (I_fun u u) / L) * Real.sqrt (h (I_fun u u) / L) = h (I_fun u u) := by
      rw [mul_assoc, hsq, mul_div_cancel₀ _ hL]
    linarith
  -- Show 2 * log(h(I(u,v))) ≥ log(h(I(u,u))) + log(h(I(v,v))) by showing
  -- g(s) := log(h(I(s, v))) - log(h(I(s, u))) is decreasing in s on [u, v] (since g'(s) ≤ 0)!
  -- Even simpler: show ∂_x log(h(I(x, y))) is decreasing in y for fixed x ∈ (0, 1)!
  -- Because for each fixed x, d/dy [∂_x log(h(I(x, y)))] = ∂_xy log(h(I(x, y))) ≤ 0!
  -- Let's prove: for any a, b ∈ (0, 1), I_fun a b ∈ (0, 1) and ∂_xy log(h(I(a, b))) ≤ 0!
  have hI_oo : ∀ a b : ℝ, 0 < a → a < 1 → 0 < b → b < 1 → 0 < I_fun a b ∧ I_fun a b < 1 := by
    intro a b ha0 ha1 hb0 hb1
    unfold I_fun
    constructor
    · apply mul_pos (mul_pos ha0 hb0)
      have : 0 < tau * (1 - a) * (1 - b) := mul_pos (mul_pos htau0 (by linarith)) (by linarith)
      linarith
    · have h1 : tau * (1 - a) * (1 - b) < (1 - a) * (1 - b) := by
        have hnn : 0 < (1 - a) * (1 - b) := mul_pos (by linarith) (by linarith)
        nlinarith
      have h2 : a * b * (1 + (1 - a) * (1 - b)) ≤ 1 := by
        have hstep : 1 - a * b * (1 + (1 - a) * (1 - b))
            = (1 - a) * (1 - b) * (1 - a * b) + a * (1 - b) + b * (1 - a) := by ring
        have h3 : 0 ≤ (1 - a) * (1 - b) * (1 - a * b) := by
          apply mul_nonneg (mul_nonneg (by linarith) (by linarith)); nlinarith
        have h4 : 0 ≤ a * (1 - b) := mul_nonneg (le_of_lt ha0) (by linarith)
        have h5 : 0 ≤ b * (1 - a) := mul_nonneg (le_of_lt hb0) (by linarith)
        linarith
      nlinarith [mul_pos ha0 hb0]
  -- Define F1(a, b) = ∂_a log(h(I(a, b))) = (hp(I(a, b)) / h(I(a, b))) * I_a(a, b)
  let Ix (a b : ℝ) : ℝ := b * (1 + tau * (1 - b) * (1 - 2 * a))
  let Iy (a b : ℝ) : ℝ := a * (1 + tau * (1 - a) * (1 - 2 * b))
  let Ixy (a b : ℝ) : ℝ := 1 + tau * (1 - 2 * a) * (1 - 2 * b)
  let F1 (a b : ℝ) : ℝ := (hp (I_fun a b) / h (I_fun a b)) * Ix a b
  have hderiv_a : ∀ a b : ℝ, 0 < a → a < 1 → 0 < b → b < 1 →
      HasDerivAt (fun s => Real.log (h (I_fun s b))) (F1 a b) a := by
    intro a b ha0 ha1 hb0 hb1
    have hI := hI_oo a b ha0 ha1 hb0 hb1
    have hdI : HasDerivAt (fun s => I_fun s b) (Ix a b) a := by
      have : (fun s => I_fun s b) = (fun s => b * (s + tau * (1 - b) * (s - s ^ 2))) := by
        ext s; unfold I_fun; ring
      rw [this]
      have h1 : HasDerivAt (fun s : ℝ => s - s ^ 2) (1 - 2 * a) a := by
        have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * a) a := by
          simpa using hasDerivAt_pow 2 a
        exact (hasDerivAt_id' a).fun_sub hsq
      exact ((hasDerivAt_id' a).fun_add (h1.const_mul (tau * (1 - b)))).const_mul b
    have hdh := (hasDerivAt_h hI.1 hI.2).comp a hdI
    have hdlog := (Real.hasDerivAt_log (ne_of_gt (h_pos hI.1 hI.2))).comp a hdh
    exact hdlog.congr_deriv (by dsimp only [F1]; ring)
  -- Now show for fixed a ∈ (0, 1), b ↦ F1 a b is antitone on (0, 1) by showing its derivative wrt b ≤ 0!
  have hF1_anti : ∀ a : ℝ, 0 < a → a < 1 → AntitoneOn (fun b => F1 a b) (Set.Icc u v) := by
    intro a ha0 ha1
    apply antitoneOn_of_deriv_nonpos (convex_Icc u v)
    · -- ContinuousOn on [u, v] ⊂ (0, 1)
      have hsub : Set.Icc u v ⊆ Set.Ioo 0 1 := fun b hb => ⟨lt_of_lt_of_le hu0 hb.1, lt_of_le_of_lt hb.2 hv1⟩
      intro b hb
      have hb' := hsub hb
      have hI := hI_oo a b ha0 ha1 hb'.1 hb'.2
      have hcI : ContinuousAt (fun s => I_fun a s) b := by unfold I_fun; fun_prop
      have hcIx : ContinuousAt (fun s => Ix a s) b := by simp only [Ix]; fun_prop
      have hch : ContinuousAt (fun s => h (I_fun a s)) b :=
        (continuousOn_h.continuousAt (Icc_mem_nhds hI.1 hI.2)).comp hcI
      have hchp : ContinuousAt (fun s => hp (I_fun a s)) b :=
        ((hasDerivAt_hp hI.1 hI.2).continuousAt).comp hcI
      exact ((hchp.div hch (ne_of_gt (h_pos hI.1 hI.2))).mul hcIx).continuousWithinAt
    · intro b hb
      rw [interior_Icc] at hb
      have hb0 : 0 < b := lt_trans hu0 hb.1
      have hb1 : b < 1 := lt_trans hb.2 hv1
      have hI := hI_oo a b ha0 ha1 hb0 hb1
      have hdI : HasDerivAt (fun s => I_fun a s) (Iy a b) b := by
        have : (fun s => I_fun a s) = (fun s => a * (s + tau * (1 - a) * (s - s ^ 2))) := by
          ext s; unfold I_fun; ring
        rw [this]
        have h1 : HasDerivAt (fun s : ℝ => s - s ^ 2) (1 - 2 * b) b := by
          have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * b) b := by simpa using hasDerivAt_pow 2 b
          exact (hasDerivAt_id' b).fun_sub hsq
        exact ((hasDerivAt_id' b).fun_add (h1.const_mul (tau * (1 - a)))).const_mul a
      have hdIx : HasDerivAt (fun s => Ix a s) (Ixy a b) b := by
        have : (fun s => Ix a s) = (fun s => s + tau * (1 - 2 * a) * (s - s ^ 2)) := by
          ext s; simp only [Ix]; ring
        rw [this]
        have h1 : HasDerivAt (fun s : ℝ => s - s ^ 2) (1 - 2 * b) b := by
          have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * b) b := by simpa using hasDerivAt_pow 2 b
          exact (hasDerivAt_id' b).fun_sub hsq
        exact (hasDerivAt_id' b).fun_add (h1.const_mul (tau * (1 - 2 * a)))
      have hdh := (hasDerivAt_h hI.1 hI.2).comp b hdI
      have hdhp := (hasDerivAt_hp hI.1 hI.2).comp b hdI
      exact ((hdhp.fun_div hdh (ne_of_gt (h_pos hI.1 hI.2))).fun_mul hdIx).differentiableAt.differentiableWithinAt
    · intro b hb
      rw [interior_Icc] at hb
      have hb0 : 0 < b := lt_trans hu0 hb.1
      have hb1 : b < 1 := lt_trans hb.2 hv1
      have hI := hI_oo a b ha0 ha1 hb0 hb1
      have hdI : HasDerivAt (fun s => I_fun a s) (Iy a b) b := by
        have : (fun s => I_fun a s) = (fun s => a * (s + tau * (1 - a) * (s - s ^ 2))) := by
          ext s; unfold I_fun; ring
        rw [this]
        have h1 : HasDerivAt (fun s : ℝ => s - s ^ 2) (1 - 2 * b) b := by
          have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * b) b := by simpa using hasDerivAt_pow 2 b
          exact (hasDerivAt_id' b).fun_sub hsq
        exact ((hasDerivAt_id' b).fun_add (h1.const_mul (tau * (1 - a)))).const_mul a
      have hdIx : HasDerivAt (fun s => Ix a s) (Ixy a b) b := by
        have : (fun s => Ix a s) = (fun s => s + tau * (1 - 2 * a) * (s - s ^ 2)) := by
          ext s; simp only [Ix]; ring
        rw [this]
        have h1 : HasDerivAt (fun s : ℝ => s - s ^ 2) (1 - 2 * b) b := by
          have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * b) b := by simpa using hasDerivAt_pow 2 b
          exact (hasDerivAt_id' b).fun_sub hsq
        exact (hasDerivAt_id' b).fun_add (h1.const_mul (tau * (1 - 2 * a)))
      have hdh := (hasDerivAt_h hI.1 hI.2).comp b hdI
      have hdhp := (hasDerivAt_hp hI.1 hI.2).comp b hdI
      have hdF1 : HasDerivAt (fun s => F1 a s)
          (((-(1 / (I_fun a b * (1 - I_fun a b))) * Iy a b * h (I_fun a b)
            - hp (I_fun a b) * (hp (I_fun a b) * Iy a b)) / (h (I_fun a b)) ^ 2) * Ix a b
            + hp (I_fun a b) / h (I_fun a b) * Ixy a b) b :=
        (hdhp.fun_div hdh (ne_of_gt (h_pos hI.1 hI.2))).fun_mul hdIx
      rw [hdF1.deriv]
      -- Simplify derivative to: a''(z)*Ix*Iy + a'(z)*Ixy where z = I_fun a b!
      set z := I_fun a b
      have hhz : 0 < h z := h_pos hI.1 hI.2
      have hderiv_simp :
          ((-(1 / (z * (1 - z))) * Iy a b * h z - hp z * (hp z * Iy a b)) / (h z) ^ 2) * Ix a b
            + hp z / h z * Ixy a b
          = -((1 / (z * (1 - z)) * h z + (hp z) ^ 2) / (h z) ^ 2) * (Ix a b * Iy a b)
            + (hp z / h z) * Ixy a b := by ring
      rw [hderiv_simp]
      -- Positivity of Ix, Iy, Ixy (explicit, fast, no slow nlinarith):
      have hB : 0 < 1 + tau * (1 - b) * (1 - 2 * a) := by
        have h1 : -(1 - b) ≤ (1 - b) * (1 - 2 * a) := by
          have : (1 - b) * (1 - 2 * a) - (-(1 - b)) = 2 * (1 - b) * (1 - a) := by ring
          have hnn : 0 ≤ 2 * (1 - b) * (1 - a) := by positivity
          linarith
        have h2 : -1 ≤ (1 - b) * (1 - 2 * a) := by linarith
        have h3 : -tau ≤ tau * ((1 - b) * (1 - 2 * a)) := by
          have := mul_le_mul_of_nonneg_left h2 (le_of_lt htau0); linarith
        linarith
      have hC : 0 < 1 + tau * (1 - a) * (1 - 2 * b) := by
        have h1 : -(1 - a) ≤ (1 - a) * (1 - 2 * b) := by
          have : (1 - a) * (1 - 2 * b) - (-(1 - a)) = 2 * (1 - a) * (1 - b) := by ring
          have hnn : 0 ≤ 2 * (1 - a) * (1 - b) := by positivity
          linarith
        have h2 : -1 ≤ (1 - a) * (1 - 2 * b) := by linarith
        have h3 : -tau ≤ tau * ((1 - a) * (1 - 2 * b)) := by
          have := mul_le_mul_of_nonneg_left h2 (le_of_lt htau0); linarith
        linarith
      have hIx_pos : 0 < Ix a b := mul_pos hb0 hB
      have hIy_pos : 0 < Iy a b := mul_pos ha0 hC
      have hIxy_pos : 0 < Ixy a b := by
        simp only [Ixy]
        have h1 : -1 ≤ (1 - 2 * a) * (1 - 2 * b) := by
          have : (1 - 2 * a) * (1 - 2 * b) + 1 = 2 * (1 - a) * (1 - b) + 2 * a * b := by ring
          have hnn : 0 ≤ 2 * (1 - a) * (1 - b) + 2 * a * b := by positivity
          linarith
        have h2 : -tau ≤ tau * ((1 - 2 * a) * (1 - 2 * b)) := by
          have := mul_le_mul_of_nonneg_left h1 (le_of_lt htau0); linarith
        linarith
      by_cases hz : z < 1 / 2
      · -- z < 1/2: use log_h_curv and z * Ixy ≤ (1 + z) * Ix * Iy!
        set Af := 1 + tau * (1 - a) * (1 - b)
        set Bf := 1 + tau * (1 - b) * (1 - 2 * a)
        set Cf := 1 + tau * (1 - a) * (1 - 2 * b)
        have hA : 1 ≤ Af := by
          have : 0 ≤ tau * (1 - a) * (1 - b) := mul_nonneg (mul_nonneg (le_of_lt htau0) (by linarith)) (by linarith)
          linarith
        have hABC : tau ≤ Af * Bf * Cf := by
          by_cases ha_h : a ≤ 1 / 2
          · by_cases hb_h : b ≤ 1 / 2
            · have hB1 : 1 ≤ Bf := by
                have : 0 ≤ tau * (1 - b) * (1 - 2 * a) := mul_nonneg (mul_nonneg (le_of_lt htau0) (by linarith)) (by linarith)
                linarith
              have hC1 : 1 ≤ Cf := by
                have : 0 ≤ tau * (1 - a) * (1 - 2 * b) := mul_nonneg (mul_nonneg (le_of_lt htau0) (by linarith)) (by linarith)
                linarith
              have h1 : 1 ≤ Af * Bf := one_le_mul_of_one_le_of_one_le hA hB1
              have h2 : 1 ≤ Af * Bf * Cf := one_le_mul_of_one_le_of_one_le h1 hC1
              linarith
            · have hB1 : 1 ≤ Bf := by
                have : 0 ≤ tau * (1 - b) * (1 - 2 * a) := mul_nonneg (mul_nonneg (le_of_lt htau0) (by linarith)) (by linarith)
                linarith
              have hC1 : 1 - tau ≤ Cf := by
                have hle : -1 ≤ (1 - a) * (1 - 2 * b) := by
                  have : (1 - a) * (1 - 2 * b) + 1 = 2 * (1 - a) * (1 - b) + a := by ring
                  have hnn : 0 ≤ 2 * (1 - a) * (1 - b) + a := by positivity
                  linarith
                have := mul_le_mul_of_nonneg_left hle (le_of_lt htau0); linarith
              have hAB : 1 ≤ Af * Bf := one_le_mul_of_one_le_of_one_le hA hB1
              have hprod : 1 - tau ≤ Af * Bf * Cf := by
                calc 1 - tau = 1 * (1 - tau) := by ring
                  _ ≤ (Af * Bf) * Cf := mul_le_mul hAB hC1 (by linarith) (by linarith)
              linarith
          · by_cases hb_h : b ≤ 1 / 2
            · have hB1 : 1 - tau ≤ Bf := by
                have hle : -1 ≤ (1 - b) * (1 - 2 * a) := by
                  have : (1 - b) * (1 - 2 * a) + 1 = 2 * (1 - b) * (1 - a) + b := by ring
                  have hnn : 0 ≤ 2 * (1 - b) * (1 - a) + b := by positivity
                  linarith
                have := mul_le_mul_of_nonneg_left hle (le_of_lt htau0); linarith
              have hC1 : 1 ≤ Cf := by
                have : 0 ≤ tau * (1 - a) * (1 - 2 * b) := mul_nonneg (mul_nonneg (le_of_lt htau0) (by linarith)) (by linarith)
                linarith
              have hAC : 1 ≤ Af * Cf := one_le_mul_of_one_le_of_one_le hA hC1
              have hprod : 1 - tau ≤ Af * Bf * Cf := by
                calc 1 - tau = 1 * (1 - tau) := by ring
                  _ ≤ (Af * Cf) * Bf := mul_le_mul hAC hB1 (by linarith) (by linarith)
                  _ = Af * Bf * Cf := by ring
              linarith
            · have hB1 : 1 - tau / 2 ≤ Bf := by
                have hle : -(1 / 2 : ℝ) ≤ (1 - b) * (1 - 2 * a) := by
                  have h1 : 0 ≤ (1 - b) * (2 * a - 1) := mul_nonneg (by linarith) (by linarith)
                  have h2 : (1 - b) * (2 * a - 1) ≤ (1 / 2) * 1 :=
                    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
                  linarith
                have := mul_le_mul_of_nonneg_left hle (le_of_lt htau0); linarith
              have hC1 : 1 - tau / 2 ≤ Cf := by
                have hle : -(1 / 2 : ℝ) ≤ (1 - a) * (1 - 2 * b) := by
                  have h2 : (1 - a) * (2 * b - 1) ≤ (1 / 2) * 1 :=
                    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
                  linarith
                have := mul_le_mul_of_nonneg_left hle (le_of_lt htau0); linarith
              have hBC : (1 - tau / 2) ^ 2 ≤ Bf * Cf := by
                rw [sq]
                exact mul_le_mul hB1 hC1 (by linarith) (by linarith)
              have hABC' : (1 - tau / 2) ^ 2 ≤ Af * Bf * Cf := by
                calc (1 - tau / 2) ^ 2 = 1 * (1 - tau / 2) ^ 2 := by ring
                  _ ≤ Af * (Bf * Cf) := mul_le_mul hA hBC (sq_nonneg _) (by linarith)
                  _ = Af * Bf * Cf := by ring
              have h916 : tau ≤ (1 - tau / 2) ^ 2 := by
                have : (1 - tau / 2) ^ 2 - tau = (1 - tau) ^ 2 - 3 / 4 * tau ^ 2 := by ring
                have h1 : 1 / 2 ≤ 1 - tau := by linarith
                have h2 : (1 / 4 : ℝ) ≤ (1 - tau) ^ 2 := by
                  calc (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
                    _ ≤ (1 - tau) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
                have h3 : tau ^ 2 ≤ 1 / 4 := by
                  calc tau ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (le_of_lt htau0) (le_of_lt htau1) 2
                    _ = 1 / 4 := by norm_num
                linarith
              linarith
        have hzIxy : z * Ixy a b ≤ (1 + z) * (Ix a b * Iy a b) := by
          have hid : z * Ixy a b - Ix a b * Iy a b = tau * a ^ 2 * b ^ 2 := by
            simp only [z, I_fun, Ix, Iy, Ixy]; ring
          have hprod : z * (Ix a b * Iy a b) = a ^ 2 * b ^ 2 * (Af * Bf * Cf) := by
            simp only [z, I_fun, Ix, Iy, Af, Bf, Cf]; ring
          have ha2b2 : 0 ≤ a ^ 2 * b ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hABC ha2b2
          linarith
        have hcurv := log_h_curv hI.1 hz
        have hhp_pos : 0 ≤ hp z / h z := by
          apply div_nonneg _ (le_of_lt hhz)
          unfold hp; apply Real.log_nonneg; rw [one_le_div hI.1]; linarith
        have h1 : (hp z / h z) * (z * Ixy a b) ≤ (hp z / h z) * ((1 + z) * (Ix a b * Iy a b)) :=
          mul_le_mul_of_nonneg_left hzIxy hhp_pos
        have h2 : (1 + z) * (hp z / h z) * (Ix a b * Iy a b)
            ≤ z * ((1 / (z * (1 - z)) * h z + (hp z) ^ 2) / (h z) ^ 2) * (Ix a b * Iy a b) :=
          mul_le_mul_of_nonneg_right hcurv (le_of_lt (mul_pos hIx_pos hIy_pos))
        have hcomb : z * ((hp z / h z) * Ixy a b)
            ≤ z * (((1 / (z * (1 - z)) * h z + (hp z) ^ 2) / (h z) ^ 2) * (Ix a b * Iy a b)) := by
          linarith
        have hdiv := le_of_mul_le_mul_left hcomb hI.1
        linarith
      · -- z ≥ 1/2: hp z ≤ 0 and the first term is ≤ 0!
        push Not at hz
        have hhp_nonpos : hp z ≤ 0 := by
          unfold hp
          exact Real.log_nonpos (le_of_lt (div_pos (by linarith [hI.2]) hI.1))
            ((div_le_one hI.1).mpr (by linarith))
        have ht1 : 0 ≤ ((1 / (z * (1 - z)) * h z + (hp z) ^ 2) / (h z) ^ 2) * (Ix a b * Iy a b) := by
          apply mul_nonneg _ (le_of_lt (mul_pos hIx_pos hIy_pos))
          apply div_nonneg _ (sq_nonneg _)
          have : 0 < z * (1 - z) := mul_pos hI.1 (by linarith [hI.2])
          positivity
        have ht2 : (hp z / h z) * Ixy a b ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hhp_nonpos (le_of_lt hhz))
            (le_of_lt hIxy_pos)
        linarith
  -- Now apply Mean Value Theorem / antitone to G(s) := log h(I(s, v)) - log h(I(s, u)) on [u, v]!
  let G (s : ℝ) : ℝ := Real.log (h (I_fun s v)) - Real.log (h (I_fun s u))
  have hG_anti : AntitoneOn G (Set.Icc u v) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc u v)
    · intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hu0 hs.1
      have hs1 : s < 1 := lt_of_le_of_lt hs.2 hv1
      exact ((hderiv_a s v hs0 hs1 (lt_trans hu0 huv') hv1).continuousAt.sub
        (hderiv_a s u hs0 hs1 hu0 (lt_trans huv' hv1)).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := lt_trans hu0 hs.1
      have hs1 : s < 1 := lt_trans hs.2 hv1
      exact ((hderiv_a s v hs0 hs1 (lt_trans hu0 huv') hv1).sub
        (hderiv_a s u hs0 hs1 hu0 (lt_trans huv' hv1))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := lt_trans hu0 hs.1
      have hs1 : s < 1 := lt_trans hs.2 hv1
      have hd : HasDerivAt G (F1 s v - F1 s u) s :=
        (hderiv_a s v hs0 hs1 (lt_trans hu0 huv') hv1).fun_sub
          (hderiv_a s u hs0 hs1 hu0 (lt_trans huv' hv1))
      rw [hd.deriv]
      have := hF1_anti s hs0 hs1 (Set.left_mem_Icc.mpr (le_of_lt huv'))
        (Set.right_mem_Icc.mpr (le_of_lt huv')) (le_of_lt huv')
      linarith
  have hGv_le_Gu : G v ≤ G u := hG_anti (Set.left_mem_Icc.mpr (le_of_lt huv'))
    (Set.right_mem_Icc.mpr (le_of_lt huv')) (le_of_lt huv')
  -- G v = log h(I(v,v)) - log h(I(v,u)) ≤ log h(I(u,v)) - log h(I(u,u)) = G u
  -- Since I(v,u) = I(u,v), this gives log h(I(u,u)) + log h(I(v,v)) ≤ 2 * log h(I(u,v))!
  have hlog_ineq : Real.log (h (I_fun u u)) + Real.log (h (I_fun v v))
      ≤ 2 * Real.log (h (I_fun u v)) := by
    simp only [G] at hGv_le_Gu
    rw [I_fun_symm v u] at hGv_le_Gu
    linarith
  have hIuu := hI_oo u u hu0 (lt_trans huv' hv1) hu0 (lt_trans huv' hv1)
  have hIvv := hI_oo v v (lt_trans hu0 huv') hv1 (lt_trans hu0 huv') hv1
  have hIuv := hI_oo u v hu0 (lt_trans huv' hv1) (lt_trans hu0 huv') hv1
  have hhuu : 0 < h (I_fun u u) := h_pos hIuu.1 hIuu.2
  have hhvv : 0 < h (I_fun v v) := h_pos hIvv.1 hIvv.2
  have hhuv : 0 < h (I_fun u v) := h_pos hIuv.1 hIuv.2
  have hexp_ineq : h (I_fun u u) * h (I_fun v v) ≤ h (I_fun u v) ^ 2 := by
    have h1 : Real.log (h (I_fun u u) * h (I_fun v v)) ≤ Real.log (h (I_fun u v) ^ 2) := by
      rw [Real.log_mul (ne_of_gt hhuu) (ne_of_gt hhvv), Real.log_pow]; push_cast; linarith
    exact (Real.log_le_log_iff (mul_pos hhuu hhvv) (sq_pos_of_pos hhuv)).mp h1
  -- Take square roots and rewrite L * phi u * phi v = sqrt(h(I(u,u)) * h(I(v,v)))!
  unfold J_fun phi
  have hL : 0 < L := L_pos
  have hprod : L * Real.sqrt (h (I_fun u u) / L) * Real.sqrt (h (I_fun v v) / L)
      = Real.sqrt (h (I_fun u u) * h (I_fun v v)) := by
    rw [mul_assoc, ← Real.sqrt_mul (div_nonneg (le_of_lt hhuu) (le_of_lt hL))]
    have h1 : h (I_fun u u) / L * (h (I_fun v v) / L) = h (I_fun u u) * h (I_fun v v) / L ^ 2 := by ring
    rw [h1, Real.sqrt_div (mul_nonneg (le_of_lt hhuu) (le_of_lt hhvv)),
        Real.sqrt_sq (le_of_lt hL), mul_div_cancel₀ _ (ne_of_gt hL)]
  rw [hprod]
  have hsq : Real.sqrt (h (I_fun u u) * h (I_fun v v)) ≤ h (I_fun u v) := by
    calc Real.sqrt (h (I_fun u u) * h (I_fun v v))
        ≤ Real.sqrt (h (I_fun u v) ^ 2) := Real.sqrt_le_sqrt hexp_ineq
      _ = h (I_fun u v) := Real.sqrt_sq (le_of_lt hhuv)
  linarith

/-- Elementary inequality `h(t) ≤ 2 L √(t(1-t))` (used for endpoint strips). -/
lemma h_le_two_L_sqrt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    h t ≤ 2 * L * Real.sqrt (t * (1 - t)) := by
  -- Actually even simpler: for t ∈ (0, 1), h(t) ≤ 2*sqrt(t*(1-t)) holds directly,
  -- wait: at t = 1/2, 2*L*sqrt(1/4) = L = h(1/2), whereas 2*sqrt(1/4) = 1 > L!
  -- Proof of sharp h(t) ≤ 2 L sqrt(t(1-t)):
  -- By symmetry, assume t ∈ (0, 1/2]. Set N(t) = 2 t(1-t) hp(t) - (1-2t) h(t).
  -- N''(t) = -(1-2t)/(t(1-t)) < 0 on (0, 1/2), N(0+) = 0, N(1/2) = 0 => N(t) ≥ 0 on (0, 1/2],
  -- so d/dt [h(t)/sqrt(t(1-t))] = N(t)/(2 (t(1-t))^(3/2)) ≥ 0 on (0, 1/2]!
  -- Hence h(t)/sqrt(t(1-t)) ≤ h(1/2)/sqrt(1/4) = 2 L!
  rcases ht0.eq_or_lt with rfl | ht0'
  · simp
  rcases ht1.eq_or_lt with rfl | ht1'
  · simp
  suffices hhalf : ∀ x : ℝ, 0 < x → x ≤ 1 / 2 → h x ≤ 2 * L * Real.sqrt (x * (1 - x)) by
    rcases le_total t (1 / 2) with hle | hge
    · exact hhalf t ht0' hle
    · rw [← h_symm t]
      have := hhalf (1 - t) (by linarith) (by linarith)
      have hmul : (1 - t) * (1 - (1 - t)) = t * (1 - t) := by ring
      rwa [hmul] at this
  intro x hx0 hx1
  -- Show N(u) = 2*u*(1-u)*hp(u) - (1-2*u)*h(u) ≥ 0 on (0, 1/2] by concavity of N on [0, 1/2]!
  let N (u : ℝ) : ℝ := 2 * u * (1 - u) * hp u - (1 - 2 * u) * h u
  have hN_cont : ContinuousOn N (Set.Icc 0 (1 / 2)) := by
    have hN_eq : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        N u = 2 * u * (1 - u) * Real.log (1 - u) - 2 * u * (1 - u) * Real.log u - (1 - 2 * u) * h u := by
      intro u hu
      rcases hu.1.eq_or_lt with rfl | hu0
      · simp [N, hp]
      · unfold N hp; rw [Real.log_div (ne_of_gt (by linarith [hu.2])) (ne_of_gt hu0)]; ring
    apply ContinuousOn.congr _ hN_eq
    have hlog1 : ContinuousOn (fun u : ℝ => 2 * u * (1 - u) * Real.log (1 - u)) (Set.Icc 0 (1 / 2)) := by
      apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.log (by fun_prop)
      intro u hu; linarith [hu.2]
    have hlog2 : ContinuousOn (fun u : ℝ => 2 * u * (1 - u) * Real.log u) (Set.Icc 0 (1 / 2)) := by
      have : (fun u : ℝ => 2 * u * (1 - u) * Real.log u) = (fun u : ℝ => (2 * (1 - u)) * (u * Real.log u)) := by
        ext u; ring
      rw [this]
      exact (Continuous.mul (by fun_prop) Real.continuous_mul_log).continuousOn
    have hh : ContinuousOn (fun u : ℝ => (1 - 2 * u) * h u) (Set.Icc 0 (1 / 2)) :=
      ContinuousOn.mul (by fun_prop) (continuousOn_h.mono (Set.Icc_subset_Icc le_rfl (by norm_num)))
    exact (hlog1.sub hlog2).sub hh
  have hN_deriv : ∀ u : ℝ, 0 < u → u < 1 / 2 →
      HasDerivAt N ((1 - 2 * u) * hp u + 2 * h u - 2) u := by
    intro u hu0 hu1
    have hu1' : u < 1 := by linarith
    have h1 : HasDerivAt (fun t : ℝ => 2 * t * (1 - t)) (2 - 4 * u) u := by
      have : (fun t : ℝ => 2 * t * (1 - t)) = (fun t : ℝ => 2 * t - 2 * t ^ 2) := by ext t; ring
      rw [this]
      have hd := ((hasDerivAt_id' u).const_mul 2).fun_sub ((hasDerivAt_pow 2 u).const_mul 2)
      convert hd using 1; ring
    have h2 : HasDerivAt (fun t : ℝ => 1 - 2 * t) (-2) u := by
      simpa using (hasDerivAt_const u (1 : ℝ)).fun_sub ((hasDerivAt_id' u).const_mul 2)
    have h3 := (h1.fun_mul (hasDerivAt_hp hu0 hu1')).fun_sub (h2.fun_mul (hasDerivAt_h hu0 hu1'))
    convert h3 using 1
    have hne : u * (1 - u) ≠ 0 := ne_of_gt (mul_pos hu0 (by linarith))
    field_simp [hne]; ring
  have hN_deriv2 : ∀ u : ℝ, 0 < u → u < 1 / 2 →
      HasDerivAt (fun t => (1 - 2 * t) * hp t + 2 * h t - 2) (-(1 - 2 * u) / (u * (1 - u))) u := by
    intro u hu0 hu1
    have hu1' : u < 1 := by linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 - 2 * t) (-2) u := by
      simpa using (hasDerivAt_const u (1 : ℝ)).fun_sub ((hasDerivAt_id' u).const_mul 2)
    have h2 := ((h1.fun_mul (hasDerivAt_hp hu0 hu1')).fun_add ((hasDerivAt_h hu0 hu1').const_mul 2)).fun_sub
      (hasDerivAt_const u (2 : ℝ))
    convert h2 using 1
    have hne : u * (1 - u) ≠ 0 := ne_of_gt (mul_pos hu0 (by linarith))
    field_simp [hne]; ring
  have hN_conc : ConcaveOn ℝ (Set.Icc 0 (1 / 2)) N := by
    apply concaveOn_of_deriv2_nonpos (convex_Icc 0 (1 / 2)) hN_cont
    · intro u hu; rw [interior_Icc] at hu
      exact (hN_deriv u hu.1 hu.2).differentiableAt.differentiableWithinAt
    · intro u hu; rw [interior_Icc] at hu
      have heq : deriv N =ᶠ[nhds u] (fun t => (1 - 2 * t) * hp t + 2 * h t - 2) := by
        filter_upwards [Ioo_mem_nhds hu.1 hu.2] with t ht
        exact (hN_deriv t ht.1 ht.2).deriv
      exact ((hN_deriv2 u hu.1 hu.2).congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
    · intro u hu; rw [interior_Icc] at hu
      have heq : deriv N =ᶠ[nhds u] (fun t => (1 - 2 * t) * hp t + 2 * h t - 2) := by
        filter_upwards [Ioo_mem_nhds hu.1 hu.2] with t ht
        exact (hN_deriv t ht.1 ht.2).deriv
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      rw [((hN_deriv2 u hu.1 hu.2).congr_of_eventuallyEq heq).deriv]
      have hpos : 0 < u * (1 - u) := mul_pos hu.1 (by linarith [hu.2])
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hu.2]) (le_of_lt hpos)
  have hN_nonneg : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), 0 ≤ N u := by
    intro u hu
    have hN0 : N 0 = 0 := by simp [N, hp]
    have hNhalf : N (1 / 2) = 0 := by
      unfold N hp; norm_num
    have hcomb := hN_conc.2 (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))
      (show 0 ≤ 1 - 2 * u by linarith [hu.2]) (show 0 ≤ 2 * u by linarith [hu.1]) (by ring)
    have hpt : (1 - 2 * u) • (0 : ℝ) + (2 * u) • (1 / 2 : ℝ) = u := by simp; ring
    rw [hpt, hN0, hNhalf, smul_zero, smul_zero, add_zero] at hcomb
    exact hcomb
  -- Now Q(u) = h(u) / sqrt(u*(1-u)) is monotone on [x, 1/2]!
  let Q (u : ℝ) : ℝ := h u / Real.sqrt (u * (1 - u))
  have hQ_mono : MonotoneOn Q (Set.Icc x (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x (1 / 2))
    · intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hx0 hu.1
      have hu1 : u < 1 := by linarith [hu.2]
      have hpos : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
      exact ((continuousOn_h.continuousAt (Icc_mem_nhds hu0 hu1)).div
        (Real.continuous_sqrt.continuousAt.comp (by fun_prop))
        (ne_of_gt (Real.sqrt_pos.mpr hpos))).continuousWithinAt
    · intro u hu; rw [interior_Icc] at hu
      have hu0 : 0 < u := lt_trans hx0 hu.1
      have hu1 : u < 1 := by linarith [hu.2]
      have hpos : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
      have hdu : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * u) u := by
        have : (fun t : ℝ => t * (1 - t)) = (fun t : ℝ => t - t ^ 2) := by ext t; ring
        rw [this]
        have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
        exact (hasDerivAt_id' u).fun_sub hsq
      have hdsq : HasDerivAt (fun t : ℝ => Real.sqrt (t * (1 - t)))
          (1 / (2 * Real.sqrt (u * (1 - u))) * (1 - 2 * u)) u :=
        (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp u hdu
      exact ((hasDerivAt_h hu0 hu1).fun_div hdsq (ne_of_gt (Real.sqrt_pos.mpr hpos))).differentiableAt.differentiableWithinAt
    · intro u hu; rw [interior_Icc] at hu
      have hu0 : 0 < u := lt_trans hx0 hu.1
      have hu1 : u < 1 := by linarith [hu.2]
      have hpos : 0 < u * (1 - u) := mul_pos hu0 (by linarith)
      have hsq_pos : 0 < Real.sqrt (u * (1 - u)) := Real.sqrt_pos.mpr hpos
      have hdu : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * u) u := by
        have : (fun t : ℝ => t * (1 - t)) = (fun t : ℝ => t - t ^ 2) := by ext t; ring
        rw [this]
        have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
        exact (hasDerivAt_id' u).fun_sub hsq
      have hdsq : HasDerivAt (fun t : ℝ => Real.sqrt (t * (1 - t)))
          (1 / (2 * Real.sqrt (u * (1 - u))) * (1 - 2 * u)) u :=
        (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp u hdu
      have hdQ : HasDerivAt Q
          ((hp u * Real.sqrt (u * (1 - u)) - h u * (1 / (2 * Real.sqrt (u * (1 - u))) * (1 - 2 * u)))
            / (Real.sqrt (u * (1 - u))) ^ 2) u :=
        (hasDerivAt_h hu0 hu1).fun_div hdsq (ne_of_gt hsq_pos)
      rw [hdQ.deriv]
      have hrew : (hp u * Real.sqrt (u * (1 - u)) - h u * (1 / (2 * Real.sqrt (u * (1 - u))) * (1 - 2 * u)))
          / (Real.sqrt (u * (1 - u))) ^ 2
          = N u / (2 * (u * (1 - u)) * Real.sqrt (u * (1 - u))) := by
        unfold N
        have hsq2 : Real.sqrt (u * (1 - u)) ^ 2 = u * (1 - u) := Real.sq_sqrt (le_of_lt hpos)
        field_simp [ne_of_gt hsq_pos, ne_of_gt hpos]
        rw [hsq2]; ring
      rw [hrew]
      exact div_nonneg (hN_nonneg u ⟨le_of_lt hu0, le_of_lt hu.2⟩) (by positivity)
  have hQle : Q x ≤ Q (1 / 2) :=
    hQ_mono (Set.left_mem_Icc.mpr hx1) (Set.right_mem_Icc.mpr hx1) hx1
  have hQhalf : Q (1 / 2) = 2 * L := by
    unfold Q
    rw [h_half]
    have h1 : (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 := by norm_num
    rw [h1, Real.sqrt_sq (by norm_num)]
    ring
  rw [hQhalf] at hQle
  have hsq_pos : 0 < Real.sqrt (x * (1 - x)) := Real.sqrt_pos.mpr (mul_pos hx0 (by linarith))
  exact (div_le_iff₀ hsq_pos).mp hQle

end UCBound
