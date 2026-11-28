module

public import UCBound.FastLog
public import UCBound.AnalyticBounds

@[expose] public section

/-!
# 2D Interval Helpers, Partial Derivatives, Witnessed Centered-Form & Hessian Checkers

Provides the shared 2D analytic + fast-interval infrastructure (using `UCBound.FastLog`)
for certifying all 6 bivariate fields of `LocalInequalities`:
- `hF_R`, `hF_v`, `hF_sim`, `hF_pos`, `hJ_b`, `hCov`.
-/

namespace UCBound.Cert2D

open UCBound UCBound.Iv UCBound.Cert UCBound.FastIv

/-! ### Common Precomputed Literal Constant Intervals -/

def qLIv : Interval := ⟨182796046504768, 182796046504801⟩
lemma qLIv_eq : qLIv = mul constIv.q LN2 := by decide
lemma mem_qLIv : mem qLIv (qStar * L) := by rw [qLIv_eq]; exact mem_mul validConstIv.hq_mem mem_LN2
lemma qLIv_lo_pos : 0 < qLIv.lo := by decide
lemma qL_lo_pos : 0 < (mul constIv.q LN2).lo := by decide
lemma constIv_p_hi_neg : constIv.p.hi < 0 := by decide
lemma p_hi_neg : constIv.p.hi < 0 := constIv_p_hi_neg

/-! ### Fast 1D Derivative Evaluators Using `FastLog` (Strict CBV) -/

def fhppIv (X : Interval) : Interval := ivCBV X fun X => hppIv X
def fIxxPIv (X : Interval) : Interval := ivCBV X fun X => IxxPIv X
def fIxxPPIv (X : Interval) : Interval := ivCBV X fun X => IxxPPIv X

@[simp] lemma fhppIv_eq (X : Interval) : fhppIv X = hppIv X := by simp [fhppIv]
@[simp] lemma fIxxPIv_eq (X : Interval) : fIxxPIv X = IxxPIv X := by simp [fIxxPIv]
@[simp] lemma fIxxPPIv_eq (X : Interval) : fIxxPPIv X = IxxPPIv X := by simp [fIxxPPIv]

def twoLNIv : Interval := mul (ofInt 2) LN2

def fastPhiP (X : Interval) : Interval :=
  ivCBV X fun X =>
  ivCBV (fIxxIv constIv X) fun ixx =>
  fdivPos (fmul (fIxxPIv X) (fastHp ixx)) (fmul (fmul (ofInt 2) LN2) (fastPhi constIv X))

def fastPhiPP (X : Interval) : Interval :=
  ivCBV X fun X =>
  ivCBV (fIxxIv constIv X) fun ixx =>
  ivCBV (fIxxPIv X) fun ixxp =>
  ivCBV (fastPhi constIv X) fun ph =>
  ivCBV (fastPhiP X) fun php =>
  ivCBV (fsub (fadd (fmul (fIxxPPIv X) (fastHp ixx)) (fmul (fsq ixxp) (fhppIv ixx)))
              (fmul (fmul (ofInt 2) LN2) (fsq php))) fun num =>
  fdivPos num (fmul (fmul (ofInt 2) LN2) ph)

def fastRP (X : Interval) : Interval :=
  ivCBV X fun X =>
  ivCBV (fmul constIv.r X) fun rx =>
  ivCBV (fsub (fsub (fadd (fmul constIv.r (fastHp rx)) (fmul qLIv (fastPhiP X))) constIv.hr)
              (fmul constIv.r (fastHp X))) fun num =>
  fdivPos num qLIv

def fastRPP (X : Interval) : Interval :=
  ivCBV X fun X =>
  ivCBV (fmul constIv.r X) fun rx =>
  ivCBV (fsub (fadd (fmul (fsq constIv.r) (fhppIv rx)) (fmul qLIv (fastPhiPP X)))
              (fmul constIv.r (fhppIv X))) fun num =>
  fdivPos num qLIv

def fastVP (X : Interval) : Interval :=
  ivCBV X fun X => fsub (fastHp X) (fmul constIv.hr (fastPhiP X))

def fastVPP (X : Interval) : Interval :=
  ivCBV X fun X => fsub (fhppIv X) (fmul constIv.hr (fastPhiPP X))

/-! ### Guards & Soundness of Fast 1D Derivatives -/

def fGuardD1 (X : Interval) : Bool :=
  ivCBV X fun X =>
  ivCBV (fmul constIv.r X) fun rx =>
  ivCBV (fIxxIv constIv X) fun ixx =>
  decide (0 < X.lo) && decide (X.lo ≤ X.hi) && decide (0 < (fsub ONE X).lo) &&
  decide (0 < rx.lo) && decide (0 < (fsub ONE rx).lo) &&
  decide (0 < ixx.lo) && decide (0 < (fsub ONE ixx).lo) &&
  decide (0 < (fmul (fmul (ofInt 2) LN2) (fastPhi constIv X)).lo)

def fGuardD2 (X : Interval) : Bool :=
  ivCBV X fun X =>
  ivCBV (fmul constIv.r X) fun rx =>
  ivCBV (fIxxIv constIv X) fun ixx =>
  fGuardD1 X &&
  decide (0 < (fmul X (fsub ONE X)).lo) &&
  decide (0 < (fmul rx (fsub ONE rx)).lo) &&
  decide (0 < (fmul ixx (fsub ONE ixx)).lo)

lemma fGuardD1_bounds {X : Interval} (hg : fGuardD1 X = true) {x : ℝ} (hx : mem X x) :
    0 < x ∧ x < 1 := by
  unfold fGuardD1 at hg
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  have hx0 : 0 < x := pos_of_lo_pos hx hg.1.1.1.1.1.1.1
  have h1mx : 0 < 1 - x := pos_of_lo_pos (mem_sub mem_ONE hx) hg.1.1.1.1.1.2
  exact ⟨hx0, by linarith⟩

lemma mem_fastPhiP_of_guard {X : Interval} (hg : fGuardD1 X = true) {x : ℝ} (hx : mem X x) :
    mem (fastPhiP X) (phiP x) := by
  have ⟨hx0, hx1⟩ := fGuardD1_bounds hg hx
  unfold fGuardD1 at hg
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  have hIxx := mem_IxxIv validConstIv hx (le_of_lt hx0) (le_of_lt hx1)
  have hhp := mem_fastHp hIxx hg.1.1.2 hg.1.2
  have hphi := mem_fastPhi validConstIv hx (le_of_lt hx0) (le_of_lt hx1)
  have hres := mem_divPos (mem_mul (mem_IxxPIv hx) hhp) (mem_mul (mem_mul (mem_ofInt 2) mem_LN2) hphi) hg.2
  unfold fastPhiP phiP; simp only [ivCBV_eq, fdivPos_eq, fmul_eq, fIxxPIv_eq, fIxxIv_eq]; simpa using hres

lemma mem_fastPhiPP_of_guard {X : Interval} (hg : fGuardD2 X = true) {x : ℝ} (hx : mem X x) :
    mem (fastPhiPP X) (phiPP x) := by
  unfold fGuardD2 at hg
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  have hgd1 := hg.1.1.1
  have ⟨hx0, hx1⟩ := fGuardD1_bounds hgd1 hx
  have hphp := mem_fastPhiP_of_guard hgd1 hx
  unfold fGuardD1 at hgd1
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgd1
  have hIxx := mem_IxxIv validConstIv hx (le_of_lt hx0) (le_of_lt hx1)
  have hhp := mem_fastHp hIxx hgd1.1.1.2 hgd1.1.2
  have hhpp := mem_hppIv hIxx hg.2
  have hphi := mem_fastPhi validConstIv hx (le_of_lt hx0) (le_of_lt hx1)
  have hnum := mem_sub (mem_add (mem_mul (mem_IxxPPIv hx) hhp) (mem_mul (mem_sq (mem_IxxPIv hx)) hhpp))
    (mem_mul (mem_mul (mem_ofInt 2) mem_LN2) (mem_sq hphp))
  have hres := mem_divPos hnum (mem_mul (mem_mul (mem_ofInt 2) mem_LN2) hphi) hgd1.2
  unfold fastPhiPP phiPP
  simp only [ivCBV_eq, fdivPos_eq, fsub_eq, fadd_eq, fmul_eq, fsq_eq, fIxxIv_eq, fIxxPIv_eq, fIxxPPIv_eq, fhppIv_eq]
  simpa using hres

lemma mem_fastRP_of_guard {X : Interval} (hg : fGuardD1 X = true) {x : ℝ} (hx : mem X x) :
    mem (fastRP X) (RP x) := by
  have hphp := mem_fastPhiP_of_guard hg hx
  unfold fGuardD1 at hg
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  have hrx := mem_mul validConstIv.hr_mem hx
  have hnum := mem_sub (mem_sub (mem_add (mem_mul validConstIv.hr_mem (mem_fastHp hrx hg.1.1.1.1.2 hg.1.1.1.2))
    (mem_mul mem_qLIv hphp)) validConstIv.hhr_mem)
    (mem_mul validConstIv.hr_mem (mem_fastHp hx hg.1.1.1.1.1.1.1 hg.1.1.1.1.1.2))
  have hres := mem_divPos hnum mem_qLIv qLIv_lo_pos
  have heq : (rStar * hp (rStar * x) + qStar * L * phiP x - hr - rStar * hp x) / (qStar * L) = RP x := by
    unfold RP; field_simp [ne_of_gt qStar_pos, ne_of_gt L_pos]; ring
  unfold fastRP; simp only [ivCBV_eq, fdivPos_eq, fsub_eq, fadd_eq, fmul_eq]; rwa [heq] at hres

lemma mem_fastRPP_of_guard {X : Interval} (hg : fGuardD2 X = true) {x : ℝ} (hx : mem X x) :
    mem (fastRPP X) (RPP x) := by
  have hphpp := mem_fastPhiPP_of_guard hg hx
  unfold fGuardD2 at hg
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  have hrx := mem_mul validConstIv.hr_mem hx
  have hnum := mem_sub (mem_add (mem_mul (mem_sq validConstIv.hr_mem) (mem_hppIv hrx hg.1.2))
    (mem_mul mem_qLIv hphpp))
    (mem_mul validConstIv.hr_mem (mem_hppIv hx hg.1.1.2))
  have hres := mem_divPos hnum mem_qLIv qLIv_lo_pos
  have heq : (rStar ^ 2 * hpp (rStar * x) + qStar * L * phiPP x - rStar * hpp x) / (qStar * L) = RPP x := by
    unfold RPP; field_simp [ne_of_gt qStar_pos, ne_of_gt L_pos]; ring
  unfold fastRPP; simp only [ivCBV_eq, fdivPos_eq, fsub_eq, fadd_eq, fmul_eq, fsq_eq, fhppIv_eq]; rwa [heq] at hres

lemma mem_fastVP_of_guard {X : Interval} (hg : fGuardD1 X = true) {x : ℝ} (hx : mem X x) :
    mem (fastVP X) (vP x) := by
  have hphp := mem_fastPhiP_of_guard hg hx
  unfold fGuardD1 at hg
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  unfold fastVP; simp only [ivCBV_eq, fsub_eq, fmul_eq]
  exact mem_sub (mem_fastHp hx hg.1.1.1.1.1.1.1 hg.1.1.1.1.1.2) (mem_mul validConstIv.hhr_mem hphp)

lemma mem_fastVPP_of_guard {X : Interval} (hg : fGuardD2 X = true) {x : ℝ} (hx : mem X x) :
    mem (fastVPP X) (vPP x) := by
  have hphpp := mem_fastPhiPP_of_guard hg hx
  unfold fGuardD2 at hg
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  unfold fastVPP; simp only [ivCBV_eq, fsub_eq, fmul_eq, fhppIv_eq]
  exact mem_sub (mem_hppIv hx hg.1.1.2) (mem_mul validConstIv.hhr_mem hphpp)

/-! ### Exact 2D Partial Derivatives of `F_fun` -/

noncomputable def Fx_fun (x y : ℝ) : ℝ :=
  y * (hp (x * y) - hp x) + qStar * L * phiP x * phi y - h y

noncomputable def Fxx_fun (x y : ℝ) : ℝ :=
  y ^ 2 * hpp (x * y) - y * hpp x + qStar * L * phiPP x * phi y

noncomputable def Fxy_fun (x y : ℝ) : ℝ :=
  hp (x * y) + (x * y) * hpp (x * y) - hp x - hp y + qStar * L * phiP x * phiP y

lemma F_fun_symm (x y : ℝ) : F_fun x y = F_fun y x := by unfold F_fun; ring

lemma hasDerivAt_F_x {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun t => F_fun t y) (Fx_fun x y) x := by
  have hxy0 : 0 < x * y := mul_pos hx0 hy0
  have hxy1 : x * y < 1 := by nlinarith
  have hd1 : HasDerivAt (fun t => h (t * y)) (hp (x * y) * y) x := by
    have := (hasDerivAt_id' x).mul_const y
    exact HasDerivAt.comp (h := fun t => t * y) x (hasDerivAt_h hxy0 hxy1) (by simpa using this)
  have hd2 : HasDerivAt (fun t => qStar * L * phi t * phi y) (qStar * L * phiP x * phi y) x := by
    have := ((hasDerivAt_phi hx0 hx1).const_mul (qStar * L)).mul_const (phi y)
    exact this.congr_deriv (by ring)
  have hd3 : HasDerivAt (fun t => y * h t) (y * hp x) x := (hasDerivAt_h hx0 hx1).const_mul y
  have hd4 : HasDerivAt (fun t => t * h y) (h y) x := by simpa using (hasDerivAt_id' x).mul_const (h y)
  have hfun : (fun t => F_fun t y) = fun t => h (t * y) + qStar * L * phi t * phi y - y * h t - t * h y := by
    ext t; unfold F_fun; ring
  rw [hfun]
  exact (((hd1.fun_add hd2).fun_sub hd3).fun_sub hd4).congr_deriv (by unfold Fx_fun; ring)

/-! ### Exact Contact Identities at `(rStar, rStar)` -/

lemma contact_F : F_fun rStar rStar = 0 ∧ Fx_fun rStar rStar = 0 := by
  have hR0 : R_fun rStar = 0 := contact_derivs.2.1
  have hR'0 : RP rStar = 0 := contact_derivs.2.2.1
  have hphir : phi rStar = 1 := phi_rStar
  have hphi'r : phiP rStar = 0 := contact_derivs.1
  have hqL_ne : qStar * L ≠ 0 := ne_of_gt (mul_pos qStar_pos L_pos)
  have hF0 : F_fun rStar rStar = 0 := by
    unfold R_fun at hR0; exact (div_eq_zero_iff.mp hR0).resolve_right hqL_ne
  have hFx0 : Fx_fun rStar rStar = 0 := by
    unfold RP at hR'0; rw [hphi'r, add_zero] at hR'0
    have hnum := (div_eq_zero_iff.mp hR'0).resolve_right hqL_ne
    unfold Fx_fun; rw [hphir, hphi'r]; unfold hr at hnum; linarith
  exact ⟨hF0, hFx0⟩

/-! ### Fast Interval Evaluators for 2D Partials & Hessians (Strict CBV) -/

def fastFx (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fclamp01 (fmul X Y)) fun xy =>
  fsub (fadd (fmul Y (fsub (fastHp xy) (fastHp X))) (fmul qLIv (fmul (fastPhiP X) (fastPhi constIv Y)))) (fastH Y)

def fastFxx (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fclamp01 (fmul X Y)) fun xy =>
  fadd (fsub (fmul (fsq Y) (fhppIv xy)) (fmul Y (fhppIv X))) (fmul qLIv (fmul (fastPhiPP X) (fastPhi constIv Y)))

def fastFxy (X Y : Interval) : Interval :=
  ivCBV X fun X => ivCBV Y fun Y =>
  ivCBV (fclamp01 (fmul X Y)) fun xy =>
  fadd (fsub (fadd (fastHp xy) (fmul xy (fhppIv xy))) (fadd (fastHp X) (fastHp Y)))
       (fmul qLIv (fmul (fastPhiP X) (fastPhiP Y)))

def fastRP_of (X hpX phpX : Interval) : Interval :=
  ivCBV (fmul constIv.r X) fun rx =>
  ivCBV (fsub (fsub (fadd (fmul constIv.r (fastHp rx)) (fmul qLIv phpX)) constIv.hr)
              (fmul constIv.r hpX)) fun num =>
  fdivPos num qLIv

def fastVP_of (hpX phpX : Interval) : Interval :=
  fsub hpX (fmul constIv.hr phpX)

def fastFx_of (X Y hpX phpX hY phY : Interval) : Interval :=
  ivCBV (fclamp01 (fmul X Y)) fun xy =>
  fsub (fadd (fmul Y (fsub (fastHp xy) hpX)) (fmul qLIv (fmul phpX phY))) hY

@[simp] lemma fastRP_of_eq (X : Interval) : fastRP_of X (fastHp X) (fastPhiP X) = fastRP X := by
  simp [fastRP_of, fastRP]
@[simp] lemma fastVP_of_eq (X : Interval) : fastVP_of (fastHp X) (fastPhiP X) = fastVP X := by
  simp [fastVP_of, fastVP]
@[simp] lemma fastFx_of_eq (X Y : Interval) :
    fastFx_of X Y (fastHp X) (fastPhiP X) (fastH Y) (fastPhi constIv Y) = fastFx X Y := by
  simp [fastFx_of, fastFx]

/-! ### 2D Domain Guards & Soundness of Fast 2D Partials/Hessians -/

def fGuard2DF (X Y : Interval) : Bool :=
  ivCBV X fun X => ivCBV Y fun Y =>
  fGuardD1 X && fGuardD1 Y &&
  ivCBV (fclamp01 (fmul X Y)) fun xy =>
  decide (0 < xy.lo) && decide (0 < (fsub ONE xy).lo)

def fGuard2DFHess (X Y : Interval) : Bool :=
  ivCBV X fun X => ivCBV Y fun Y =>
  fGuardD2 X && fGuardD2 Y &&
  ivCBV (fclamp01 (fmul X Y)) fun xy =>
  decide (0 < xy.lo) && decide (0 < (fsub ONE xy).lo) &&
  decide (0 < (fmul xy (fsub ONE xy)).lo)

lemma mem_fastFx {X Y : Interval} (hg : fGuard2DF X Y = true) {x y : ℝ} (hx : mem X x) (hy : mem Y y) :
    mem (fastFx X Y) (Fx_fun x y) := by
  unfold fGuard2DF at hg
  simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hgX, hgY⟩, ⟨hxy0, hxy1⟩⟩ := hg
  have ⟨hx0, hx1⟩ := fGuardD1_bounds hgX hx
  have ⟨hy0, hy1⟩ := fGuardD1_bounds hgY hy
  have hxy := mem_clamp01 (mem_mul hx hy) (by positivity) (by nlinarith)
  have hgX' := hgX; unfold fGuardD1 at hgX'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgX'
  have hres := mem_sub (mem_add (mem_mul hy (mem_sub (mem_fastHp hxy hxy0 hxy1)
      (mem_fastHp hx hgX'.1.1.1.1.1.1.1 hgX'.1.1.1.1.1.2)))
    (mem_mul mem_qLIv (mem_mul (mem_fastPhiP_of_guard hgX hx) (mem_fastPhi validConstIv hy (le_of_lt hy0) (le_of_lt hy1)))))
    (mem_fastH hy (le_of_lt hy0) (le_of_lt hy1))
  have heq : y * (hp (x * y) - hp x) + qStar * L * (phiP x * phi y) - h y = Fx_fun x y := by unfold Fx_fun; ring
  unfold fastFx; simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, fadd_eq]; rwa [heq] at hres

lemma mem_fastFxx {X Y : Interval} (hg : fGuard2DFHess X Y = true) {x y : ℝ} (hx : mem X x) (hy : mem Y y) :
    mem (fastFxx X Y) (Fxx_fun x y) := by
  unfold fGuard2DFHess at hg
  simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hgX, hgY⟩, ⟨⟨_, _⟩, hxy_p⟩⟩ := hg
  have hgX' := hgX; unfold fGuardD2 at hgX'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgX'
  have hgY' := hgY; unfold fGuardD2 at hgY'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgY'
  have ⟨hx0, hx1⟩ := fGuardD1_bounds hgX'.1.1.1 hx
  have ⟨hy0, hy1⟩ := fGuardD1_bounds hgY'.1.1.1 hy
  have hxy := mem_clamp01 (mem_mul hx hy) (by positivity) (by nlinarith)
  have hres := mem_add (mem_sub (mem_mul (mem_sq hy) (mem_hppIv hxy hxy_p))
      (mem_mul hy (mem_hppIv hx hgX'.1.1.2)))
    (mem_mul mem_qLIv (mem_mul (mem_fastPhiPP_of_guard hgX hx) (mem_fastPhi validConstIv hy (le_of_lt hy0) (le_of_lt hy1))))
  have heq : y ^ 2 * hpp (x * y) - y * hpp x + qStar * L * (phiPP x * phi y) = Fxx_fun x y := by unfold Fxx_fun; ring
  unfold fastFxx; simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, fadd_eq, fsq_eq, fhppIv_eq]; rwa [heq] at hres

lemma mem_fastFxy {X Y : Interval} (hg : fGuard2DFHess X Y = true) {x y : ℝ} (hx : mem X x) (hy : mem Y y) :
    mem (fastFxy X Y) (Fxy_fun x y) := by
  unfold fGuard2DFHess at hg
  simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hgX, hgY⟩, ⟨⟨hxy0, hxy1⟩, hxy_p⟩⟩ := hg
  have hgX' := hgX; unfold fGuardD2 at hgX'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgX'
  have hgY' := hgY; unfold fGuardD2 at hgY'
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgY'
  have ⟨hx0, hx1⟩ := fGuardD1_bounds hgX'.1.1.1 hx
  have ⟨hy0, hy1⟩ := fGuardD1_bounds hgY'.1.1.1 hy
  have hxy := mem_clamp01 (mem_mul hx hy) (by positivity) (by nlinarith)
  have hgX1 := hgX'.1.1.1; unfold fGuardD1 at hgX1
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgX1
  have hgY1 := hgY'.1.1.1; unfold fGuardD1 at hgY1
  simp only [ivCBV_eq, fsub_eq, fmul_eq, fIxxIv_eq, Bool.and_eq_true, decide_eq_true_eq] at hgY1
  have hres := mem_add (mem_sub (mem_add (mem_fastHp hxy hxy0 hxy1) (mem_mul hxy (mem_hppIv hxy hxy_p)))
      (mem_add (mem_fastHp hx hgX1.1.1.1.1.1.1.1 hgX1.1.1.1.1.1.2)
               (mem_fastHp hy hgY1.1.1.1.1.1.1.1 hgY1.1.1.1.1.1.2)))
    (mem_mul mem_qLIv (mem_mul (mem_fastPhiP_of_guard hgX'.1.1.1 hx) (mem_fastPhiP_of_guard hgY'.1.1.1 hy)))
  have heq : hp (x * y) + x * y * hpp (x * y) - (hp x + hp y) + qStar * L * (phiP x * phiP y) = Fxy_fun x y := by
    unfold Fxy_fun; ring
  unfold fastFxy; simp only [ivCBV_eq, fclamp01_eq, fmul_eq, fsub_eq, fadd_eq, fhppIv_eq]; rwa [heq] at hres

/-! ### Witness-Carrying 2D Tree Checker, Centered Form & Contact-Square Hessian Test -/

/-- Leaf witness tag: tells the kernel checker which exact test to run (zero wasted evaluations!). -/
inductive LeafW where
  | direct : LeafW
  | centered : LeafW
  | hess : LeafW
  | skip : LeafW
  deriving Repr, DecidableEq

/-- Explicit-midpoint witness-carrying 2D binary tree. -/
inductive Tree2DW where
  | leaf (w : LeafW) : Tree2DW
  | cutX (m : ℤ) (l r : Tree2DW) : Tree2DW
  | cutY (m : ℤ) (l r : Tree2DW) : Tree2DW
  deriving Repr, DecidableEq

def check2DW (pred : LeafW → Interval → Interval → Bool) (xlo xhi ylo yhi : ℤ) : Tree2DW → Bool
  | .leaf w => pred w ⟨xlo, xhi⟩ ⟨ylo, yhi⟩
  | .cutX m l r =>
    decide (xlo ≤ m) && decide (m ≤ xhi) &&
    check2DW pred xlo m ylo yhi l && check2DW pred m xhi ylo yhi r
  | .cutY m l r =>
    decide (ylo ≤ m) && decide (m ≤ yhi) &&
    check2DW pred xlo xhi ylo m l && check2DW pred xlo xhi m yhi r

theorem check2DW_sound {pred : LeafW → Interval → Interval → Bool} {P : ℝ → ℝ → Prop}
    (hpred : ∀ w X Y, pred w X Y = true → ∀ x y, mem X x → mem Y y → P x y)
    {xlo xhi ylo yhi : ℤ} {t : Tree2DW} (hchk : check2DW pred xlo xhi ylo yhi t = true)
    {x y : ℝ} (hx : mem ⟨xlo, xhi⟩ x) (hy : mem ⟨ylo, yhi⟩ y) : P x y := by
  induction t generalizing xlo xhi ylo yhi with
  | leaf w => exact hpred w ⟨xlo, xhi⟩ ⟨ylo, yhi⟩ hchk x y hx hy
  | cutX m l r ihl ihr =>
    unfold check2DW at hchk; simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases le_total x ((m : ℝ) / SCALE) with hxm | hmx
    · exact ihl hchk.1.2 ⟨hx.1, hxm⟩ hy
    · exact ihr hchk.2 ⟨hmx, hx.2⟩ hy
  | cutY m l r ihl ihr =>
    unfold check2DW at hchk; simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases le_total y ((m : ℝ) / SCALE) with hym | hmy
    · exact ihl hchk.1.2 hx ⟨hy.1, hym⟩
    · exact ihr hchk.2 hx ⟨hmy, hy.2⟩

/-- Symmetric 2D soundness: only checks boxes that intersect `{x ≤ y}` (allows `.skip` when `Y.hi < X.lo`). -/
theorem check2DW_sym_sound {pred : LeafW → Interval → Interval → Bool} {P : ℝ → ℝ → Prop}
    (hpred : ∀ w X Y, pred w X Y = true → ∀ x y, mem X x → mem Y y → x ≤ y → P x y)
    {xlo xhi ylo yhi : ℤ} {t : Tree2DW} (hchk : check2DW pred xlo xhi ylo yhi t = true)
    {x y : ℝ} (hx : mem ⟨xlo, xhi⟩ x) (hy : mem ⟨ylo, yhi⟩ y) (hxy : x ≤ y) : P x y :=
  check2DW_sound (P := fun u v => u ≤ v → P u v) (fun w X Y hok u v hu hv huv => hpred w X Y hok u v hu hv huv)
    hchk hx hy hxy

/-- Witnessed 2D centered-form positivity check (strict CBV, evaluates ONLY direct or ONLY centered!). -/
def centered2DWPos (G_iv Gx_iv Gy_iv : Interval → Interval → Interval)
    (w : LeafW) (X Y : Interval) : Bool :=
  match w with
  | .direct => decide (0 < (G_iv X Y).lo)
  | .centered =>
    intCBV ((X.lo + X.hi) / 2) fun mx =>
    intCBV ((Y.lo + Y.hi) / 2) fun my =>
    intCBV (max (mx - X.lo) (X.hi - mx)) fun hx =>
    intCBV (max (my - Y.lo) (Y.hi - my)) fun hy =>
    ivCBV (G_iv (pt mx) (pt my)) fun gm =>
    intCBV (absHi (Gx_iv X Y)) fun Mx =>
    intCBV (absHi (Gy_iv (pt mx) Y)) fun My =>
    decide (0 < (fsub (fsub gm (fmul (pt Mx) (pt hx))) (fmul (pt My) (pt hy))).lo)
  | _ => false

theorem centered2DWPos_sound
    {G Gx Gy : ℝ → ℝ → ℝ}
    {G_iv Gx_iv Gy_iv : Interval → Interval → Interval}
    {w : LeafW} {X Y : Interval}
    (hXle : X.lo ≤ X.hi) (hYle : Y.lo ≤ Y.hi)
    (hG_mem : ∀ I J, X.lo ≤ I.lo → I.hi ≤ X.hi → Y.lo ≤ J.lo → J.hi ≤ Y.hi →
      ∀ u v, mem I u → mem J v → mem (G_iv I J) (G u v))
    (hGx_mem : ∀ u v, mem X u → mem Y v → mem (Gx_iv X Y) (Gx u v))
    (hGy_mem_pt : ∀ v, mem Y v → mem (Gy_iv (pt ((X.lo + X.hi) / 2)) Y) (Gy (((X.lo + X.hi) / 2 : ℤ) / (SCALE : ℝ)) v))
    (hcontX : ∀ v ∈ Set.Icc ((Y.lo : ℝ) / SCALE) ((Y.hi : ℝ) / SCALE),
      ContinuousOn (fun t => G t v) (Set.Icc ((X.lo : ℝ) / SCALE) ((X.hi : ℝ) / SCALE)))
    (hderivX : ∀ v ∈ Set.Icc ((Y.lo : ℝ) / SCALE) ((Y.hi : ℝ) / SCALE),
      ∀ u ∈ Set.Ioo ((X.lo : ℝ) / SCALE) ((X.hi : ℝ) / SCALE), HasDerivAt (fun t => G t v) (Gx u v) u)
    (hcontY : ContinuousOn (fun s => G (((X.lo + X.hi) / 2 : ℤ) / (SCALE : ℝ)) s)
      (Set.Icc ((Y.lo : ℝ) / SCALE) ((Y.hi : ℝ) / SCALE)))
    (hderivY : ∀ v ∈ Set.Ioo ((Y.lo : ℝ) / SCALE) ((Y.hi : ℝ) / SCALE),
      HasDerivAt (fun s => G (((X.lo + X.hi) / 2 : ℤ) / (SCALE : ℝ)) s)
        (Gy (((X.lo + X.hi) / 2 : ℤ) / (SCALE : ℝ)) v) v)
    (hok : centered2DWPos G_iv Gx_iv Gy_iv w X Y = true)
    {x y : ℝ} (hx : mem X x) (hy : mem Y y) :
    0 < G x y := by
  have hS := SCALE_pos
  cases w with
  | direct =>
    unfold centered2DWPos at hok; simp only [decide_eq_true_eq] at hok
    exact pos_of_lo_pos (hG_mem X Y le_rfl le_rfl le_rfl le_rfl x y hx hy) hok
  | centered =>
    unfold centered2DWPos at hok
    simp only [intCBV_eq, ivCBV_eq, fsub_eq, fmul_eq, decide_eq_true_eq] at hok
    set mx : ℤ := (X.lo + X.hi) / 2
    set my : ℤ := (Y.lo + Y.hi) / 2
    set hx_i : ℤ := max (mx - X.lo) (X.hi - mx)
    set hy_i : ℤ := max (my - Y.lo) (Y.hi - my)
    set Mx_i : ℤ := absHi (Gx_iv X Y)
    set My_i : ℤ := absHi (Gy_iv (pt mx) Y)
    have hmx_lo : X.lo ≤ mx := by omega
    have hmx_hi : mx ≤ X.hi := by omega
    have hmy_lo : Y.lo ≤ my := by omega
    have hmy_hi : my ≤ Y.hi := by omega
    have hmx_mem : mem X ((mx : ℝ) / SCALE) :=
      ⟨div_le_div_of_nonneg_right (by exact_mod_cast hmx_lo) (le_of_lt hS),
       div_le_div_of_nonneg_right (by exact_mod_cast hmx_hi) (le_of_lt hS)⟩
    have hmy_mem : mem Y ((my : ℝ) / SCALE) :=
      ⟨div_le_div_of_nonneg_right (by exact_mod_cast hmy_lo) (le_of_lt hS),
       div_le_div_of_nonneg_right (by exact_mod_cast hmy_hi) (le_of_lt hS)⟩
    have hgm := hG_mem (pt mx) (pt my) hmx_lo hmx_hi hmy_lo hmy_hi ((mx : ℝ) / SCALE) ((my : ℝ) / SCALE) (mem_pt mx) (mem_pt my)
    have hMx_nn : (0 : ℝ) ≤ (Mx_i : ℝ) / SCALE :=
      le_trans (abs_nonneg _) (abs_le_absHi (hGx_mem x y hx hy))
    have hMy_nn : (0 : ℝ) ≤ (My_i : ℝ) / SCALE :=
      le_trans (abs_nonneg _) (abs_le_absHi (hGy_mem_pt y hy))
    have hradX : max ((mx : ℝ) / SCALE - (X.lo : ℝ) / SCALE) ((X.hi : ℝ) / SCALE - (mx : ℝ) / SCALE)
        = (hx_i : ℝ) / SCALE := by
      have h1 : (mx : ℝ) / SCALE - (X.lo : ℝ) / SCALE = ((mx - X.lo : ℤ) : ℝ) / SCALE := by push_cast; ring
      have h2 : (X.hi : ℝ) / SCALE - (mx : ℝ) / SCALE = ((X.hi - mx : ℤ) : ℝ) / SCALE := by push_cast; ring
      rw [h1, h2]
      rcases le_total (mx - X.lo) (X.hi - mx) with h | h
      · rw [max_eq_right (div_le_div_of_nonneg_right (by exact_mod_cast h) (le_of_lt hS))]
        simp [hx_i, max_eq_right h]
      · rw [max_eq_left (div_le_div_of_nonneg_right (by exact_mod_cast h) (le_of_lt hS))]
        simp [hx_i, max_eq_left h]
    have hradY : max ((my : ℝ) / SCALE - (Y.lo : ℝ) / SCALE) ((Y.hi : ℝ) / SCALE - (my : ℝ) / SCALE)
        = (hy_i : ℝ) / SCALE := by
      have h1 : (my : ℝ) / SCALE - (Y.lo : ℝ) / SCALE = ((my - Y.lo : ℤ) : ℝ) / SCALE := by push_cast; ring
      have h2 : (Y.hi : ℝ) / SCALE - (my : ℝ) / SCALE = ((Y.hi - my : ℤ) : ℝ) / SCALE := by push_cast; ring
      rw [h1, h2]
      rcases le_total (my - Y.lo) (Y.hi - my) with h | h
      · rw [max_eq_right (div_le_div_of_nonneg_right (by exact_mod_cast h) (le_of_lt hS))]
        simp [hy_i, max_eq_right h]
      · rw [max_eq_left (div_le_div_of_nonneg_right (by exact_mod_cast h) (le_of_lt hS))]
        simp [hy_i, max_eq_left h]
    have hmvt := mvt_centered_2d (G := G) (Gx := Gx) (Gy := Gy)
      (ax := (X.lo : ℝ) / SCALE) (bx := (X.hi : ℝ) / SCALE)
      (ay := (Y.lo : ℝ) / SCALE) (by_ := (Y.hi : ℝ) / SCALE)
      (mx := (mx : ℝ) / SCALE) (my := (my : ℝ) / SCALE)
      (Mx := (Mx_i : ℝ) / SCALE) (My := (My_i : ℝ) / SCALE)
      hMx_nn hMy_nn hcontX hderivX
      (fun v hv u hu => abs_le_absHi (hGx_mem u v ⟨le_of_lt hu.1, le_of_lt hu.2⟩ hv))
      hcontY hderivY
      (fun v hv => abs_le_absHi (hGy_mem_pt v ⟨le_of_lt hv.1, le_of_lt hv.2⟩))
      hmx_mem hmy_mem hx hy
    rw [hradX, hradY] at hmvt
    have hlb := mem_sub (mem_sub hgm (mem_mul (mem_pt Mx_i) (mem_pt hx_i))) (mem_mul (mem_pt My_i) (mem_pt hy_i))
    have hpos : (0 : ℝ) < ((sub (sub (G_iv (pt mx) (pt my)) (mul (pt Mx_i) (pt hx_i))) (mul (pt My_i) (pt hy_i))).lo : ℝ) / SCALE :=
      div_pos (by exact_mod_cast hok) hS
    linarith [hlb.1]
  | hess => simp [centered2DWPos] at hok
  | skip => simp [centered2DWPos] at hok

/-- Positive-definite Hessian test on a box `(X, Y)` (strict CBV): `Hxx > 0`, `Hyy > 0`, `Hxx.lo * Hyy.lo > |Hxy|^2`. -/
def hess2DPD (Hxx Hyy Hxy : Interval) : Bool :=
  ivCBV Hxx fun Hxx =>
  decide (0 < Hxx.lo) &&
  ivCBV Hyy fun Hyy =>
  decide (0 < Hyy.lo) &&
  intCBV (absHi Hxy) fun hxy =>
  decide (hxy * hxy < Hxx.lo * Hyy.lo)

lemma hess2DPD_quad_nonneg {Hxx Hyy Hxy : Interval} (hok : hess2DPD Hxx Hyy Hxy = true)
    {a b c dx dy : ℝ} (ha : mem Hxx a) (hb : mem Hyy b) (hc : mem Hxy c) :
    0 ≤ a * dx ^ 2 + 2 * c * dx * dy + b * dy ^ 2 := by
  unfold hess2DPD at hok
  simp only [ivCBV_eq, intCBV_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨ha0, ⟨hb0, hdet⟩⟩ := hok
  have hS := SCALE_pos
  have ha_pos : 0 < a := pos_of_lo_pos ha ha0
  have hb_pos : 0 < b := pos_of_lo_pos hb hb0
  have hc_abs : |c| ≤ (absHi Hxy : ℝ) / SCALE := abs_le_absHi hc
  have hdetR : ((absHi Hxy : ℝ) / SCALE) ^ 2 < ((Hxx.lo : ℝ) / SCALE) * ((Hyy.lo : ℝ) / SCALE) := by
    rw [div_pow, div_mul_div_comm, ← sq (SCALE : ℝ), div_lt_div_iff_of_pos_right (sq_pos_of_pos hS)]
    have : ((absHi Hxy : ℝ) * (absHi Hxy : ℝ)) < (Hxx.lo : ℝ) * (Hyy.lo : ℝ) := by exact_mod_cast hdet
    nlinarith
  have hc2_lt : c ^ 2 < a * b := by
    have h1 : c ^ 2 ≤ ((absHi Hxy : ℝ) / SCALE) ^ 2 := by
      rw [← sq_abs c]; exact pow_le_pow_left₀ (abs_nonneg c) hc_abs 2
    have h2 : ((Hxx.lo : ℝ) / SCALE) * ((Hyy.lo : ℝ) / SCALE) ≤ a * b :=
      mul_le_mul ha.1 hb.1 (div_nonneg (by exact_mod_cast le_of_lt hb0) (le_of_lt hS)) (le_of_lt ha_pos)
    linarith
  -- Complete the square: a * dx^2 + 2 c dx dy + b dy^2 = a * (dx + (c/a) dy)^2 + (b - c^2/a) dy^2 ≥ 0!
  have hcs : a * dx ^ 2 + 2 * c * dx * dy + b * dy ^ 2
      = a * (dx + c / a * dy) ^ 2 + (a * b - c ^ 2) / a * dy ^ 2 := by
    field_simp [ne_of_gt ha_pos]; ring
  rw [hcs]
  have h1 : 0 ≤ a * (dx + c / a * dy) ^ 2 := mul_nonneg (le_of_lt ha_pos) (sq_nonneg _)
  have h2 : 0 ≤ (a * b - c ^ 2) / a * dy ^ 2 :=
    mul_nonneg (div_nonneg (by linarith) (le_of_lt ha_pos)) (sq_nonneg _)
  linarith

/-- Directional 2D Taylor-2 positivity on a convex square `[lo, hi]^2` containing `(rStar, rStar)`!
    Reduces directly to 1D `nonneg_of_deriv2_nonneg` along `s ↦ G (rStar + s*(x-rStar)) (rStar + s*(y-rStar))`! -/
theorem nonneg_of_hess_pd_square
    {G Gx Gy Hxx Hyy Hxy : ℝ → ℝ → ℝ} {lo hi : ℝ}
    (hr_lo : lo ≤ rStar) (hr_hi : rStar ≤ hi)
    (hG0 : G rStar rStar = 0) (hGx0 : Gx rStar rStar = 0) (hGy0 : Gy rStar rStar = 0)
    (hderiv_G : ∀ u v, lo ≤ u → u ≤ hi → lo ≤ v → v ≤ hi →
      ∀ (x y s : ℝ),
        HasDerivAt (fun t => G (rStar + t * (x - rStar)) (rStar + t * (y - rStar)))
          (Gx (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (x - rStar) +
           Gy (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (y - rStar)) s)
    (hderiv_dG : ∀ u v, lo ≤ u → u ≤ hi → lo ≤ v → v ≤ hi →
      ∀ (x y s : ℝ),
        HasDerivAt (fun t => Gx (rStar + t * (x - rStar)) (rStar + t * (y - rStar)) * (x - rStar) +
                             Gy (rStar + t * (x - rStar)) (rStar + t * (y - rStar)) * (y - rStar))
          (Hxx (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (x - rStar) ^ 2 +
           2 * Hxy (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (x - rStar) * (y - rStar) +
           Hyy (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (y - rStar) ^ 2) s)
    (hpd : ∀ u v, lo ≤ u → u ≤ hi → lo ≤ v → v ≤ hi →
      ∀ dx dy, 0 ≤ Hxx u v * dx ^ 2 + 2 * Hxy u v * dx * dy + Hyy u v * dy ^ 2)
    {x y : ℝ} (hx_lo : lo ≤ x) (hx_hi : x ≤ hi) (hy_lo : lo ≤ y) (hy_hi : y ≤ hi) :
    0 ≤ G x y := by
  set dx := x - rStar
  set dy := y - rStar
  set g : ℝ → ℝ := fun t => G (rStar + t * dx) (rStar + t * dy)
  set g' : ℝ → ℝ := fun t => Gx (rStar + t * dx) (rStar + t * dy) * dx + Gy (rStar + t * dx) (rStar + t * dy) * dy
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      lo ≤ rStar + t * dx ∧ rStar + t * dx ≤ hi ∧ lo ≤ rStar + t * dy ∧ rStar + t * dy ≤ hi := fun t ht => by
    have hx_rew : rStar + t * dx = (1 - t) * rStar + t * x := by simp only [dx]; ring
    have hy_rew : rStar + t * dy = (1 - t) * rStar + t * y := by simp only [dy]; ring
    rw [hx_rew, hy_rew]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [ht.1, ht.2]
  have hg1 : g 1 = G x y := by simp only [g, dx, dy]; ring_nf
  rw [← hg1]
  exact nonneg_of_deriv2_nonneg (a := 0) (b := 1) (r := 0) le_rfl (by norm_num)
    (fun t ht => by
      have hs := hseg t ht
      exact (hderiv_G _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 x y t).continuousAt.continuousWithinAt)
    (fun t ht => by
      have hs := hseg t (Set.Ioo_subset_Icc_self ht)
      exact hderiv_G _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 x y t)
    (fun t ht => by
      have hs := hseg t ht
      exact (hderiv_dG _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 x y t).continuousAt.continuousWithinAt)
    (fun t ht => by
      have hs := hseg t (Set.Ioo_subset_Icc_self ht)
      exact hderiv_dG _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 x y t)
    (fun t ht => by
      have hs := hseg t (Set.Ioo_subset_Icc_self ht)
      exact hpd _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 dx dy)
    (by simp [g, hG0])
    (by simp [hGx0, hGy0])
    1 ⟨by norm_num, le_rfl⟩

/-- Chain-rule helper for directional derivatives along a 2D line `(r + t*dx, r + t*dy)`:
    given partial derivatives `fx, fy` of `f` on `(0,1)^2`, proves `HasDerivAt` of `t ↦ f (x₀ + t dx) (y₀ + t dy)`.
    NOTE: for our explicit formulas (`F_fun`, `J_fun`, `phi`, `R_fun`, `v_fun`, `b_fun`), each is an explicit
    algebraic combination of 1D functions `h`, `hp`, `phi`, `phiP`, `R_fun`, `RP`, `v_fun`, `vP`, `b_fun`, `bP`
    evaluated at `u(t)`, `v(t)`, `u(t) * v(t)`, or `I_fun (u(t)) (v(t))`, so 1D `HasDerivAt.comp` handles them
    in 5 lines without needing Fréchet derivatives at all! -/
lemma hasDerivAt_F_line {x y s : ℝ}
    (hu0 : 0 < rStar + s * (x - rStar)) (hu1 : rStar + s * (x - rStar) < 1)
    (hv0 : 0 < rStar + s * (y - rStar)) (hv1 : rStar + s * (y - rStar) < 1) :
    HasDerivAt (fun t => F_fun (rStar + t * (x - rStar)) (rStar + t * (y - rStar)))
      (Fx_fun (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (x - rStar) +
       Fx_fun (rStar + s * (y - rStar)) (rStar + s * (x - rStar)) * (y - rStar)) s := by
  set dx := x - rStar; set dy := y - rStar
  set u : ℝ → ℝ := fun t => rStar + t * dx
  set v : ℝ → ℝ := fun t => rStar + t * dy
  have hdu : HasDerivAt u dx s := by simpa [u] using ((hasDerivAt_id' s).mul_const dx).const_add rStar
  have hdv : HasDerivAt v dy s := by simpa [v] using ((hasDerivAt_id' s).mul_const dy).const_add rStar
  have huv0 : 0 < u s * v s := mul_pos hu0 hv0
  have huv1 : u s * v s < 1 := by nlinarith
  have hd_huv : HasDerivAt (fun t => h (u t * v t)) (hp (u s * v s) * (dx * v s + u s * dy)) s :=
    HasDerivAt.comp (h := fun t => u t * v t) s (hasDerivAt_h huv0 huv1) (hdu.fun_mul hdv)
  have hd_hu : HasDerivAt (fun t => h (u t)) (hp (u s) * dx) s :=
    HasDerivAt.comp (h := u) s (hasDerivAt_h hu0 hu1) hdu
  have hd_hv : HasDerivAt (fun t => h (v t)) (hp (v s) * dy) s :=
    HasDerivAt.comp (h := v) s (hasDerivAt_h hv0 hv1) hdv
  have hd_pu : HasDerivAt (fun t => phi (u t)) (phiP (u s) * dx) s :=
    HasDerivAt.comp (h := u) s (hasDerivAt_phi hu0 hu1) hdu
  have hd_pv : HasDerivAt (fun t => phi (v t)) (phiP (v s) * dy) s :=
    HasDerivAt.comp (h := v) s (hasDerivAt_phi hv0 hv1) hdv
  have hd_q : HasDerivAt (fun t => qStar * L * phi (u t) * phi (v t)) _ s :=
    ((hd_pu.const_mul (qStar * L)).fun_mul hd_pv)
  have hd_vh : HasDerivAt (fun t => v t * h (u t)) _ s := hdv.fun_mul hd_hu
  have hd_uh : HasDerivAt (fun t => u t * h (v t)) _ s := hdu.fun_mul hd_hv
  have hfun : (fun t => F_fun (u t) (v t)) = fun t => h (u t * v t) + qStar * L * phi (u t) * phi (v t) - v t * h (u t) - u t * h (v t) := by
    ext t; unfold F_fun; ring
  rw [show (fun t => F_fun (rStar + t * (x - rStar)) (rStar + t * (y - rStar))) = fun t => F_fun (u t) (v t) from rfl, hfun]
  exact (((hd_huv.fun_add hd_q).fun_sub hd_vh).fun_sub hd_uh).congr_deriv (by
    unfold Fx_fun; rw [mul_comm (v s) (u s)]; ring)

lemma hasDerivAt_Fx_line {x y s : ℝ}
    (hu0 : 0 < rStar + s * (x - rStar)) (hu1 : rStar + s * (x - rStar) < 1)
    (hv0 : 0 < rStar + s * (y - rStar)) (hv1 : rStar + s * (y - rStar) < 1) :
    HasDerivAt (fun t => Fx_fun (rStar + t * (x - rStar)) (rStar + t * (y - rStar)))
      (Fxx_fun (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (x - rStar) +
       Fxy_fun (rStar + s * (x - rStar)) (rStar + s * (y - rStar)) * (y - rStar)) s := by
  set dx := x - rStar; set dy := y - rStar
  set u : ℝ → ℝ := fun t => rStar + t * dx
  set v : ℝ → ℝ := fun t => rStar + t * dy
  have hdu : HasDerivAt u dx s := by simpa [u] using ((hasDerivAt_id' s).mul_const dx).const_add rStar
  have hdv : HasDerivAt v dy s := by simpa [v] using ((hasDerivAt_id' s).mul_const dy).const_add rStar
  have huv0 : 0 < u s * v s := mul_pos hu0 hv0
  have huv1 : u s * v s < 1 := by nlinarith
  have hd_hpuv : HasDerivAt (fun t => hp (u t * v t)) (hpp (u s * v s) * (dx * v s + u s * dy)) s :=
    HasDerivAt.comp (h := fun t => u t * v t) s (hasDerivAt_hp huv0 huv1) (hdu.fun_mul hdv)
  have hd_hpu : HasDerivAt (fun t => hp (u t)) (hpp (u s) * dx) s :=
    HasDerivAt.comp (h := u) s (hasDerivAt_hp hu0 hu1) hdu
  have hd_hv : HasDerivAt (fun t => h (v t)) (hp (v s) * dy) s :=
    HasDerivAt.comp (h := v) s (hasDerivAt_h hv0 hv1) hdv
  have hd_ppu : HasDerivAt (fun t => phiP (u t)) (phiPP (u s) * dx) s :=
    HasDerivAt.comp (h := u) s (hasDerivAt_phiP hu0 hu1) hdu
  have hd_pv : HasDerivAt (fun t => phi (v t)) (phiP (v s) * dy) s :=
    HasDerivAt.comp (h := v) s (hasDerivAt_phi hv0 hv1) hdv
  have hd1 := hdv.fun_mul (hd_hpuv.fun_sub hd_hpu)
  have hd2 := (hd_ppu.const_mul (qStar * L)).fun_mul hd_pv
  have hfun : (fun t => Fx_fun (u t) (v t)) = fun t => v t * (hp (u t * v t) - hp (u t)) + qStar * L * phiP (u t) * phi (v t) - h (v t) := by
    ext t; unfold Fx_fun; ring
  rw [show (fun t => Fx_fun (rStar + t * (x - rStar)) (rStar + t * (y - rStar))) = fun t => Fx_fun (u t) (v t) from rfl, hfun]
  exact ((hd1.fun_add hd2).fun_sub hd_hv).congr_deriv (by unfold Fxx_fun Fxy_fun; ring)

end UCBound.Cert2D
