module

public import UCBound.Interval
public import UCBound.SubsetAvg

@[expose] public section

/-!
# Interval Enclosures for Kernel Functions, Mean-Value Bounds, and Tree Checkers

This module extends `UCBound.Iv` with:
1. `ConstIv` and `ValidConstIv`: certified 50-bit interval enclosures of all constants in `Basic.lean`
   and `SubsetAvg.lean`.
2. Zero-wrapping monotonicity-exact `IxxIv` and `phiIv`, plus sound interval evaluators for
   `I_fun`, `F_fun`, `J_fun`, `R_fun`, `v_fun`, `b_fun`, `hp`.
3. Generic 1D and 2D binary-tree certificate checkers (`Tree1D`, `Tree2D`) with pure-kernel soundness
   lemmas (usable with `decide`, zero `native_decide`).
4. 1D and 2D centered-form (mean-value) soundness helpers for tight certification near contact points.
-/

namespace UCBound.Iv

open UCBound

/-! ### Constant Enclosure Structure -/

/-- Bundle of 50-bit scaled-integer interval enclosures for all real constants of the proof. -/
structure ConstIv where
  r : Interval
  m : Interval
  q : Interval
  hr : Interval
  p : Interval
  c : Interval
  tau : Interval
  gamma : Interval
  alpha : Interval
  t0 : Interval
  bm : Interval
  D : Interval
  eStar : Interval
  beta : Interval
  b0 : Interval
  W : Interval
  eta : Interval
  sqrtL : Interval
  deriving Repr, DecidableEq

/-- Validity predicate linking a `ConstIv` bundle to the exact real constants. -/
structure ValidConstIv (C : ConstIv) : Prop where
  hr_mem : mem C.r rStar
  hm_mem : mem C.m mStar
  hq_mem : mem C.q qStar
  hhr_mem : mem C.hr hr
  hp_mem : mem C.p pStar
  hc_mem : mem C.c cParam
  htau_mem : mem C.tau tau
  hgamma_mem : mem C.gamma gamma
  halpha_mem : mem C.alpha alpha
  ht0_mem : mem C.t0 t0
  hbm_mem : mem C.bm bm
  hD_mem : mem C.D DParam
  heStar_mem : mem C.eStar eStar
  hbeta_mem : mem C.beta betaParam
  hb0_mem : mem C.b0 b0Param
  hW_mem : mem C.W WParam
  heta_mem : mem C.eta etaParam
  hsqrtL_mem : mem C.sqrtL (Real.sqrt L)
  htau_pos : 0 < tau
  htau_lt_half : tau < 1 / 2

/-! ### Extra Basic Interval Helpers -/

/-- Exact rational interval for `p / q` with `q > 0` (convenience wrapper). -/
def rat (p : ℤ) (q : ℕ) : Interval := ofRat p q

/-- Scaled integer constant `1`. -/
def ONE : Interval := ofInt 1

lemma mem_ONE : mem ONE 1 := by simpa [ONE] using mem_ofInt 1

/-- Point interval at integer scaled value `a`. -/
def pt (a : ℤ) : Interval := ⟨a, a⟩

lemma mem_pt (a : ℤ) : mem (pt a) ((a : ℝ) / (SCALE : ℝ)) := ⟨le_rfl, le_rfl⟩

/-- Upper bound on `|x|` for `x ∈ I`, as a scaled integer. -/
def absHi (I : Interval) : ℤ := max (|I.lo|) (|I.hi|)

lemma abs_le_absHi {I : Interval} {x : ℝ} (hx : mem I x) :
    |x| ≤ (absHi I : ℝ) / (SCALE : ℝ) := by
  have hS := SCALE_pos
  rw [abs_le]
  have h1 : -(absHi I : ℤ) ≤ I.lo := by
    unfold absHi
    have := le_max_left (|I.lo|) (|I.hi|)
    have := neg_abs_le I.lo
    omega
  have h2 : I.hi ≤ absHi I := by
    unfold absHi
    have := le_max_right (|I.lo|) (|I.hi|)
    have := le_abs_self I.hi
    omega
  constructor
  · have h1R : -((absHi I : ℝ) / SCALE) ≤ (I.lo : ℝ) / SCALE := by
      rw [← neg_div]; apply div_le_div_of_nonneg_right _ (le_of_lt hS)
      exact_mod_cast h1
    exact le_trans h1R hx.1
  · have h2R : (I.hi : ℝ) / SCALE ≤ (absHi I : ℝ) / SCALE :=
      div_le_div_of_nonneg_right (by exact_mod_cast h2) (le_of_lt hS)
    exact le_trans hx.2 h2R

/-- Clamp an interval to `[0, 1]` (assuming it intersects `[0, 1]`). -/
def clamp01 (I : Interval) : Interval :=
  ⟨max 0 (min (SCALE : ℤ) I.lo), max 0 (min (SCALE : ℤ) I.hi)⟩

lemma mem_clamp01 {I : Interval} {x : ℝ} (hx : mem I x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (clamp01 I) x := by
  have hS := SCALE_pos
  unfold clamp01 mem
  dsimp only
  constructor
  · rw [Int.cast_max, Int.cast_min, Int.cast_zero, Int.cast_natCast]
    rw [max_div_pos (le_of_lt hS), zero_div]
    apply max_le hx0
    rw [min_div_pos (le_of_lt hS), div_self SCALE_ne_zero]
    exact le_trans (min_le_right _ _) hx.1
  · rw [Int.cast_max, Int.cast_min, Int.cast_zero, Int.cast_natCast]
    rw [max_div_pos (le_of_lt hS), zero_div]
    apply le_max_of_le_right
    rw [min_div_pos (le_of_lt hS), div_self SCALE_ne_zero]
    exact le_min hx1 hx.2

/-- Sound enclosure of `x / y` when `I.lo > 0` or `J.hi < 0` (handles negative divisor `pStar`). -/
def divNeg (I J : Interval) : Interval :=
  neg (divPos I (neg J))

lemma mem_divNeg {I J : Interval} {x y : ℝ} (hx : mem I x) (hy : mem J y) (hJ : J.hi < 0) :
    mem (divNeg I J) (x / y) := by
  have hny : mem (neg J) (-y) := mem_neg hy
  have hpos : 0 < (neg J).lo := by unfold neg; dsimp; omega
  have h1 := mem_neg (mem_divPos hx hny hpos)
  unfold divNeg
  simpa [div_neg, neg_neg] using h1

/-! ### Monotonicity of `I_fun x x` and Zero-Wrapping `IxxIv`, `phiIv` -/

/-- `I_fun x x = x^2 * (1 + tau * (1 - x)^2)` is monotone on `[0, 1]` for `0 < tau < 1/2`. -/
lemma monotoneOn_Ixx (htau0 : 0 < tau) (htau1 : tau < 1 / 2) :
    MonotoneOn (fun x => I_fun x x) (Set.Icc 0 1) := by
  have hd_all : ∀ x : ℝ, HasDerivAt (fun t => I_fun t t)
      (2 * x * (1 + tau * (1 - x) * (1 - 2 * x))) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t * t) (1 * x + x * 1) x :=
      (hasDerivAt_id' x).fun_mul (hasDerivAt_id' x)
    have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id' x)
    have h3 : HasDerivAt (fun t : ℝ => (1 - t) * (1 - t)) ((-1) * (1 - x) + (1 - x) * (-1)) x :=
      h2.fun_mul h2
    have h4 : HasDerivAt (fun t : ℝ => 1 + tau * ((1 - t) * (1 - t)))
        (0 + tau * ((-1) * (1 - x) + (1 - x) * (-1))) x :=
      (hasDerivAt_const x (1 : ℝ)).fun_add (h3.const_mul tau)
    have hprod := h1.fun_mul h4
    have hfun : (fun t => I_fun t t) = fun t => (t * t) * (1 + tau * ((1 - t) * (1 - t))) := by
      ext t; unfold I_fun; ring
    rw [hfun]
    exact hprod.congr_deriv (by ring)
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · apply Continuous.continuousOn; unfold I_fun; fun_prop
  · intro x _; exact (hd_all x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hd_all x).deriv]
    have hquad : -(1 / 8 : ℝ) ≤ (1 - x) * (1 - 2 * x) := by
      have : (1 - x) * (1 - 2 * x) + 1 / 8 = 2 * (x - 3 / 4) ^ 2 := by ring
      nlinarith [sq_nonneg (x - 3 / 4)]
    have hfac : 0 ≤ 1 + tau * (1 - x) * (1 - 2 * x) := by nlinarith
    exact mul_nonneg (by linarith [hx.1]) hfac

/-- Point enclosure of `I_fun (a/SCALE) (a/SCALE)` for `0 ≤ a ≤ SCALE`. -/
def IxxPt (C : ConstIv) (a : ℤ) : Interval :=
  let x := pt a
  let omx := pt ((SCALE : ℤ) - a)
  clamp01 (mul (sq x) (add ONE (mul C.tau (sq omx))))

lemma mem_IxxPt {C : ConstIv} (hC : ValidConstIv C) {a : ℤ} (ha0 : 0 ≤ a) (ha1 : a ≤ (SCALE : ℤ)) :
    mem (IxxPt C a) (I_fun ((a : ℝ) / SCALE) ((a : ℝ) / SCALE)) := by
  have hx0 : (0 : ℝ) ≤ (a : ℝ) / SCALE := div_nonneg (by exact_mod_cast ha0) (le_of_lt SCALE_pos)
  have hx1 : (a : ℝ) / SCALE ≤ 1 := (div_le_one SCALE_pos).mpr (by exact_mod_cast ha1)
  have hI01 := I_fun_mem_Icc (le_of_lt hC.htau_pos) (by linarith [hC.htau_lt_half]) hx0 hx1 hx0 hx1
  apply mem_clamp01 _ hI01.1 hI01.2
  have hx : mem (pt a) ((a : ℝ) / SCALE) := mem_pt a
  have homx : mem (pt ((SCALE : ℤ) - a)) (1 - (a : ℝ) / SCALE) := by
    unfold pt mem; push_cast
    rw [sub_div, div_self SCALE_ne_zero]; exact ⟨le_rfl, le_rfl⟩
  have h := mem_mul (mem_sq hx) (mem_add mem_ONE (mem_mul hC.htau_mem (mem_sq homx)))
  unfold I_fun
  convert h using 1; ring

/-- Zero-wrapping monotonicity-exact enclosure of `I_fun x x` on `X ∩ [0, 1]`. -/
def IxxIv (C : ConstIv) (X : Interval) : Interval :=
  let a := max 0 (min (SCALE : ℤ) X.lo)
  let b := max 0 (min (SCALE : ℤ) X.hi)
  ⟨(IxxPt C a).lo, (IxxPt C b).hi⟩

lemma mem_IxxIv {C : ConstIv} (hC : ValidConstIv C) {X : Interval} {x : ℝ}
    (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (IxxIv C X) (I_fun x x) := by
  have hcl := mem_clamp01 hx hx0 hx1
  set a : ℤ := max 0 (min (SCALE : ℤ) X.lo)
  set b : ℤ := max 0 (min (SCALE : ℤ) X.hi)
  have ha0 : 0 ≤ a := le_max_left _ _
  have ha1 : a ≤ (SCALE : ℤ) := max_le (by unfold SCALE; omega) (min_le_left _ _)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hb1 : b ≤ (SCALE : ℤ) := max_le (by unfold SCALE; omega) (min_le_left _ _)
  have haR0 : (0 : ℝ) ≤ (a : ℝ) / SCALE := div_nonneg (by exact_mod_cast ha0) (le_of_lt SCALE_pos)
  have haR1 : (a : ℝ) / SCALE ≤ 1 := (div_le_one SCALE_pos).mpr (by exact_mod_cast ha1)
  have hbR0 : (0 : ℝ) ≤ (b : ℝ) / SCALE := div_nonneg (by exact_mod_cast hb0) (le_of_lt SCALE_pos)
  have hbR1 : (b : ℝ) / SCALE ≤ 1 := (div_le_one SCALE_pos).mpr (by exact_mod_cast hb1)
  have hmono := monotoneOn_Ixx hC.htau_pos hC.htau_lt_half
  have hIa := mem_IxxPt hC ha0 ha1
  have hIb := mem_IxxPt hC hb0 hb1
  exact ⟨le_trans hIa.1 (hmono ⟨haR0, haR1⟩ ⟨hx0, hx1⟩ hcl.1),
         le_trans (hmono ⟨hx0, hx1⟩ ⟨hbR0, hbR1⟩ hcl.2) hIb.2⟩

/-- Zero-wrapping enclosure of `phi x = √(h(I_fun x x) / L)`. -/
def phiIv (C : ConstIv) (X : Interval) : Interval :=
  clamp01 (sqrt (divPos (hIv (IxxIv C X)) LN2))

lemma mem_phiIv {C : ConstIv} (hC : ValidConstIv C) {X : Interval} {x : ℝ}
    (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (phiIv C X) (phi x) := by
  have hI01 := I_fun_mem_Icc (le_of_lt hC.htau_pos) (by linarith [hC.htau_lt_half]) hx0 hx1 hx0 hx1
  have hI := mem_IxxIv hC hx hx0 hx1
  have hh := mem_hIv hI hI01.1 hI01.2
  have hdiv := mem_divPos hh mem_LN2 (by unfold LN2; decide)
  have hdiv_nn : 0 ≤ h (I_fun x x) / L := div_nonneg (h_nonneg hI01.1 hI01.2) (le_of_lt L_pos)
  have hsq := mem_sqrt hdiv hdiv_nn
  have hphi0 : 0 ≤ phi x := phi_nonneg x
  have hphi1 : phi x ≤ 1 := by
    unfold phi
    have : h (I_fun x x) / L ≤ 1 := (div_le_one L_pos).mpr (h_le_L hI01.1 hI01.2)
    calc Real.sqrt (h (I_fun x x) / L) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt this
      _ = 1 := Real.sqrt_one
  exact mem_clamp01 hsq hphi0 hphi1

/-! ### Kernel Function Interval Evaluators -/

/-- Interval enclosure of `I_fun x y` on `X × Y ⊆ [0, 1]²`. -/
def IxyIv (C : ConstIv) (X Y : Interval) : Interval :=
  clamp01 (mul (mul X Y) (add ONE (mul C.tau (mul (sub ONE X) (sub ONE Y)))))

lemma mem_IxyIv {C : ConstIv} (hC : ValidConstIv C) {X Y : Interval} {x y : ℝ}
    (hx : mem X x) (hy : mem Y y) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    mem (IxyIv C X Y) (I_fun x y) := by
  have hI01 := I_fun_mem_Icc (le_of_lt hC.htau_pos) (by linarith [hC.htau_lt_half]) hx0 hx1 hy0 hy1
  apply mem_clamp01 _ hI01.1 hI01.2
  unfold I_fun
  have h1 := mem_mul (mem_mul hx hy)
    (mem_add mem_ONE (mem_mul hC.htau_mem (mem_mul (mem_sub mem_ONE hx) (mem_sub mem_ONE hy))))
  convert h1 using 1; ring

/-- Interval enclosure of `F_fun x y = h(xy) + q L phi(x) phi(y) - y h(x) - x h(y)`. -/
def FIv (C : ConstIv) (X Y : Interval) : Interval :=
  let hxy := hIv (clamp01 (mul X Y))
  let hx := hIv X
  let hy := hIv Y
  let px := phiIv C X
  let py := phiIv C Y
  sub (sub (add hxy (mul (mul C.q LN2) (mul px py))) (mul Y hx)) (mul X hy)

lemma mem_FIv {C : ConstIv} (hC : ValidConstIv C) {X Y : Interval} {x y : ℝ}
    (hx : mem X x) (hy : mem Y y) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    mem (FIv C X Y) (F_fun x y) := by
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxy1 : x * y ≤ 1 := by nlinarith
  have hhxy := mem_hIv (mem_clamp01 (mem_mul hx hy) hxy0 hxy1) hxy0 hxy1
  have hhx := mem_hIv hx hx0 hx1
  have hhy := mem_hIv hy hy0 hy1
  have hpx := mem_phiIv hC hx hx0 hx1
  have hpy := mem_phiIv hC hy hy0 hy1
  unfold FIv F_fun
  have hres := mem_sub (mem_sub (mem_add hhxy (mem_mul (mem_mul hC.hq_mem mem_LN2) (mem_mul hpx hpy)))
    (mem_mul hy hhx)) (mem_mul hx hhy)
  convert hres using 1; ring

/-- Interval enclosure of `J_fun x y = h(I_fun x y) - L phi(x) phi(y)`. -/
def JIv (C : ConstIv) (X Y : Interval) : Interval :=
  sub (hIv (IxyIv C X Y)) (mul LN2 (mul (phiIv C X) (phiIv C Y)))

lemma mem_JIv {C : ConstIv} (hC : ValidConstIv C) {X Y : Interval} {x y : ℝ}
    (hx : mem X x) (hy : mem Y y) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    mem (JIv C X Y) (J_fun x y) := by
  have hI01 := I_fun_mem_Icc (le_of_lt hC.htau_pos) (by linarith [hC.htau_lt_half]) hx0 hx1 hy0 hy1
  have hhI := mem_hIv (mem_IxyIv hC hx hy hx0 hx1 hy0 hy1) hI01.1 hI01.2
  have hpx := mem_phiIv hC hx hx0 hx1
  have hpy := mem_phiIv hC hy hy0 hy1
  unfold JIv J_fun
  have hres := mem_sub hhI (mem_mul mem_LN2 (mem_mul hpx hpy))
  convert hres using 1; ring

/-- Interval enclosure of `R_fun x = F_fun rStar x / (qStar * L)` (needs `(mul C.q LN2).lo > 0`). -/
def RIv (C : ConstIv) (X : Interval) : Interval :=
  divPos (FIv C C.r X) (mul C.q LN2)

lemma mem_RIv {C : ConstIv} (hC : ValidConstIv C) (hqL : 0 < (mul C.q LN2).lo)
    {X : Interval} {x : ℝ} (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (RIv C X) (R_fun x) := by
  have hr0 := le_of_lt rStar_pos
  have hr1 := le_of_lt rStar_lt_one
  exact mem_divPos (mem_FIv hC hC.hr_mem hx hr0 hr1 hx0 hx1) (mem_mul hC.hq_mem mem_LN2) hqL

/-- Interval enclosure of `v_fun x = h x - hr * phi x`. -/
def vIv (C : ConstIv) (X : Interval) : Interval :=
  sub (hIv X) (mul C.hr (phiIv C X))

lemma mem_vIv {C : ConstIv} (hC : ValidConstIv C) {X : Interval} {x : ℝ}
    (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (vIv C X) (v_fun x) :=
  mem_sub (mem_hIv hx hx0 hx1) (mem_mul hC.hhr_mem (mem_phiIv hC hx hx0 hx1))

/-- Interval enclosure of `b_fun x = x - h x / pStar - cParam * phi x` (needs `C.p.hi < 0`). -/
def bIv (C : ConstIv) (X : Interval) : Interval :=
  sub (sub X (divNeg (hIv X) C.p)) (mul C.c (phiIv C X))

lemma mem_bIv {C : ConstIv} (hC : ValidConstIv C) (hp : C.p.hi < 0)
    {X : Interval} {x : ℝ} (hx : mem X x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mem (bIv C X) (b_fun x) :=
  mem_sub (mem_sub hx (mem_divNeg (mem_hIv hx hx0 hx1) hC.hp_mem hp))
    (mem_mul hC.hc_mem (mem_phiIv hC hx hx0 hx1))

/-- Interval enclosure of `hp x = log((1 - x) / x) = log(1 - x) - log x` on `(0, 1)`. -/
def hpIv (X : Interval) : Interval :=
  sub (log (sub ONE X)) (log X)

lemma mem_hpIv {X : Interval} {x : ℝ} (hx : mem X x)
    (hX0 : 0 < X.lo) (hX1 : 0 < (sub ONE X).lo) :
    mem (hpIv X) (hp x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (div_pos (by exact_mod_cast hX0) SCALE_pos) hx.1
  have h1mx := mem_sub mem_ONE hx
  have h1mx_pos : 0 < 1 - x := lt_of_lt_of_le (div_pos (by exact_mod_cast hX1) SCALE_pos) h1mx.1
  have h := mem_sub (mem_log h1mx hX1) (mem_log hx hX0)
  unfold hp
  rw [Real.log_div (ne_of_gt h1mx_pos) (ne_of_gt hx_pos)]
  exact h

/-! ### Generic 1D and 2D Binary-Tree Certificate Checkers -/

/-- Compact binary partition tree for 1D interval certificates. -/
inductive Tree1D where
  | leaf : Tree1D
  | node (l r : Tree1D) : Tree1D
  | split (m : ℤ) (l r : Tree1D) : Tree1D
  deriving Repr, DecidableEq

/-- Check a predicate over `[lo/SCALE, hi/SCALE]` via a `Tree1D`. -/
def check1D (pred : Interval → Bool) (lo hi : ℤ) : Tree1D → Bool
  | .leaf => pred ⟨lo, hi⟩
  | .node l r =>
    let m := (lo + hi) / 2
    lo ≤ m && m ≤ hi && check1D pred lo m l && check1D pred m hi r
  | .split m l r =>
    lo ≤ m && m ≤ hi && check1D pred lo m l && check1D pred m hi r

theorem check1D_sound {pred : Interval → Bool} {P : ℝ → Prop}
    (hpred : ∀ I, pred I = true → ∀ x, mem I x → P x)
    {lo hi : ℤ} {t : Tree1D} (hchk : check1D pred lo hi t = true)
    {x : ℝ} (hx : mem ⟨lo, hi⟩ x) : P x := by
  induction t generalizing lo hi with
  | leaf =>
    exact hpred ⟨lo, hi⟩ hchk x hx
  | node l r ihl ihr =>
    unfold check1D at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    set m := (lo + hi) / 2
    rcases le_total x ((m : ℝ) / SCALE) with hxm | hmx
    · exact ihl hchk.1.2 ⟨hx.1, hxm⟩
    · exact ihr hchk.2 ⟨hmx, hx.2⟩
  | split m l r ihl ihr =>
    unfold check1D at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases le_total x ((m : ℝ) / SCALE) with hxm | hmx
    · exact ihl hchk.1.2 ⟨hx.1, hxm⟩
    · exact ihr hchk.2 ⟨hmx, hx.2⟩

/-- Compact binary partition tree for 2D interval certificates. -/
inductive Tree2D where
  | leaf : Tree2D
  | splitX (l r : Tree2D) : Tree2D
  | splitY (l r : Tree2D) : Tree2D
  | cutX (m : ℤ) (l r : Tree2D) : Tree2D
  | cutY (m : ℤ) (l r : Tree2D) : Tree2D
  deriving Repr, DecidableEq

/-- Check a 2D predicate over `[xlo, xhi] × [ylo, yhi]` (scaled by `SCALE`). -/
def check2D (pred : Interval → Interval → Bool) (xlo xhi ylo yhi : ℤ) : Tree2D → Bool
  | .leaf => pred ⟨xlo, xhi⟩ ⟨ylo, yhi⟩
  | .splitX l r =>
    let m := (xlo + xhi) / 2
    xlo ≤ m && m ≤ xhi && check2D pred xlo m ylo yhi l && check2D pred m xhi ylo yhi r
  | .splitY l r =>
    let m := (ylo + yhi) / 2
    ylo ≤ m && m ≤ yhi && check2D pred xlo xhi ylo m l && check2D pred xlo xhi m yhi r
  | .cutX m l r =>
    xlo ≤ m && m ≤ xhi && check2D pred xlo m ylo yhi l && check2D pred m xhi ylo yhi r
  | .cutY m l r =>
    ylo ≤ m && m ≤ yhi && check2D pred xlo xhi ylo m l && check2D pred xlo xhi m yhi r

theorem check2D_sound {pred : Interval → Interval → Bool} {P : ℝ → ℝ → Prop}
    (hpred : ∀ Ix Iy, pred Ix Iy = true → ∀ x y, mem Ix x → mem Iy y → P x y)
    {xlo xhi ylo yhi : ℤ} {t : Tree2D} (hchk : check2D pred xlo xhi ylo yhi t = true)
    {x y : ℝ} (hx : mem ⟨xlo, xhi⟩ x) (hy : mem ⟨ylo, yhi⟩ y) : P x y := by
  induction t generalizing xlo xhi ylo yhi with
  | leaf =>
    exact hpred ⟨xlo, xhi⟩ ⟨ylo, yhi⟩ hchk x y hx hy
  | splitX l r ihl ihr =>
    unfold check2D at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    set m := (xlo + xhi) / 2
    rcases le_total x ((m : ℝ) / SCALE) with hxm | hmx
    · exact ihl hchk.1.2 ⟨hx.1, hxm⟩ hy
    · exact ihr hchk.2 ⟨hmx, hx.2⟩ hy
  | splitY l r ihl ihr =>
    unfold check2D at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    set m := (ylo + yhi) / 2
    rcases le_total y ((m : ℝ) / SCALE) with hym | hmy
    · exact ihl hchk.1.2 hx ⟨hy.1, hym⟩
    · exact ihr hchk.2 hx ⟨hmy, hy.2⟩
  | cutX m l r ihl ihr =>
    unfold check2D at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases le_total x ((m : ℝ) / SCALE) with hxm | hmx
    · exact ihl hchk.1.2 ⟨hx.1, hxm⟩ hy
    · exact ihr hchk.2 ⟨hmx, hx.2⟩ hy
  | cutY m l r ihl ihr =>
    unfold check2D at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases le_total y ((m : ℝ) / SCALE) with hym | hmy
    · exact ihl hchk.1.2 hx ⟨hy.1, hym⟩
    · exact ihr hchk.2 hx ⟨hmy, hy.2⟩

/-- Symmetric 2D checker: automatically skips boxes where `yhi < xlo` (proves `P x y` for `x ≤ y`). -/
def check2DLe (pred : Interval → Interval → Bool) (xlo xhi ylo yhi : ℤ) : Tree2D → Bool :=
  check2D (fun Ix Iy => decide (Iy.hi < Ix.lo) || pred Ix Iy) xlo xhi ylo yhi

theorem check2DLe_sound {pred : Interval → Interval → Bool} {P : ℝ → ℝ → Prop}
    (hpred : ∀ Ix Iy, pred Ix Iy = true → ∀ x y, mem Ix x → mem Iy y → P x y)
    {xlo xhi ylo yhi : ℤ} {t : Tree2D} (hchk : check2DLe pred xlo xhi ylo yhi t = true)
    {x y : ℝ} (hx : mem ⟨xlo, xhi⟩ x) (hy : mem ⟨ylo, yhi⟩ y) (hxy : x ≤ y) : P x y := by
  exact check2D_sound (P := fun a b => a ≤ b → P a b) (by
    intro Ix Iy hok a b ha hb hab
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hok
    rcases hok with hskip | hp
    · exfalso
      have h1 : (Iy.hi : ℝ) / SCALE < (Ix.lo : ℝ) / SCALE :=
        div_lt_div_of_pos_right (by exact_mod_cast hskip) SCALE_pos
      linarith [ha.1, hb.2]
    · exact hpred Ix Iy hp a b ha hb) hchk hx hy hxy

/-! ### 1D & 2D Mean-Value (Centered-Form) Bounds -/

/-- 1D centered-form lower bound via Mean Value Theorem:
    If `f` is continuous on `[a, b]` with `HasDerivAt f (f' u) u` on `(a, b)`,
    `0 ≤ M` and `|f' u| ≤ M` for all `u ∈ (a, b)`, and `m ∈ [a, b]`, then for all `x ∈ [a, b]`:
    `f m - M * max (m - a) (b - m) ≤ f x`. -/
lemma mvt_centered_1d {f f' : ℝ → ℝ} {a b m M : ℝ}
    (hM0 : 0 ≤ M)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt f (f' u) u)
    (hM : ∀ u ∈ Set.Ioo a b, |f' u| ≤ M)
    (hm : m ∈ Set.Icc a b)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    f m - M * max (m - a) (b - m) ≤ f x := by
  rcases lt_trichotomy x m with hxm | rfl | hmx
  · have hsub : Set.Icc x m ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hm.2
    have hsubo : Set.Ioo x m ⊆ Set.Ioo a b := fun u hu => ⟨lt_of_le_of_lt hx.1 hu.1, lt_of_lt_of_le hu.2 hm.2⟩
    obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope f f' hxm (hcont.mono hsub)
      (fun u hu => hderiv u (hsubo hu))
    have hdiff : f m - f x = f' c * (m - x) := by
      have hne : m - x ≠ 0 := ne_of_gt (sub_pos.mpr hxm)
      field_simp [hne] at hce ⊢; linarith
    have habs : f m - f x ≤ M * (m - x) := by
      rw [hdiff]
      calc f' c * (m - x) ≤ |f' c| * (m - x) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
        _ ≤ M * (m - x) := mul_le_mul_of_nonneg_right (hM c (hsubo hc)) (by linarith)
    have hmx_le : m - x ≤ max (m - a) (b - m) := le_trans (by linarith [hx.1]) (le_max_left _ _)
    have := mul_le_mul_of_nonneg_left hmx_le hM0
    linarith
  · have hmax0 : 0 ≤ max (x - a) (b - x) := le_trans (by linarith [hx.1]) (le_max_left _ _)
    have := mul_nonneg hM0 hmax0
    linarith
  · have hsub : Set.Icc m x ⊆ Set.Icc a b := Set.Icc_subset_Icc hm.1 hx.2
    have hsubo : Set.Ioo m x ⊆ Set.Ioo a b := fun u hu => ⟨lt_of_le_of_lt hm.1 hu.1, lt_of_lt_of_le hu.2 hx.2⟩
    obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope f f' hmx (hcont.mono hsub)
      (fun u hu => hderiv u (hsubo hu))
    have hdiff : f x - f m = f' c * (x - m) := by
      have hne : x - m ≠ 0 := ne_of_gt (sub_pos.mpr hmx)
      field_simp [hne] at hce ⊢; linarith
    have habs : f m - f x ≤ M * (x - m) := by
      have : -(f' c) ≤ |f' c| := neg_le_abs _
      have h1 : f m - f x = -(f' c) * (x - m) := by linarith
      rw [h1]
      calc -(f' c) * (x - m) ≤ |f' c| * (x - m) := mul_le_mul_of_nonneg_right this (by linarith)
        _ ≤ M * (x - m) := mul_le_mul_of_nonneg_right (hM c (hsubo hc)) (by linarith)
    have hxm_le : x - m ≤ max (m - a) (b - m) := le_trans (by linarith [hx.2]) (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left hxm_le hM0
    linarith

/-- 2D centered-form lower bound via two 1D MVT steps:
    `G mx my - Mx * max(mx - ax, bx - mx) - My * max(my - ay, by - my) ≤ G x y`. -/
lemma mvt_centered_2d {G Gx Gy : ℝ → ℝ → ℝ} {ax bx ay by_ mx my Mx My : ℝ}
    (hMx0 : 0 ≤ Mx) (hMy0 : 0 ≤ My)
    (hcontX : ∀ y ∈ Set.Icc ay by_, ContinuousOn (fun x => G x y) (Set.Icc ax bx))
    (hderivX : ∀ y ∈ Set.Icc ay by_, ∀ x ∈ Set.Ioo ax bx, HasDerivAt (fun t => G t y) (Gx x y) x)
    (hMx : ∀ y ∈ Set.Icc ay by_, ∀ x ∈ Set.Ioo ax bx, |Gx x y| ≤ Mx)
    (hcontY : ContinuousOn (fun y => G mx y) (Set.Icc ay by_))
    (hderivY : ∀ y ∈ Set.Ioo ay by_, HasDerivAt (fun t => G mx t) (Gy mx y) y)
    (hMy : ∀ y ∈ Set.Ioo ay by_, |Gy mx y| ≤ My)
    (hmx : mx ∈ Set.Icc ax bx) (hmy : my ∈ Set.Icc ay by_)
    {x y : ℝ} (hx : x ∈ Set.Icc ax bx) (hy : y ∈ Set.Icc ay by_) :
    G mx my - Mx * max (mx - ax) (bx - mx) - My * max (my - ay) (by_ - my) ≤ G x y := by
  have h1 := mvt_centered_1d hMx0 (hcontX y hy) (hderivX y hy) (hMx y hy) hmx hx
  have h2 := mvt_centered_1d hMy0 hcontY hderivY hMy hmy hy
  linarith

end UCBound.Iv
