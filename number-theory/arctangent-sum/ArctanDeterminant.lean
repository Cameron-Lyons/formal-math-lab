module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace Arxiv.«2607.05739»

abbrev inverseCoeffOne : ℝ := -5/12
abbrev inverseCoeffThree : ℝ := 13/192

/-- The approximation for twice the centered inverse phase, with a uniform
bound H for the error coefficient. -/
def InversePhaseApprox (H t u : ℝ) : Prop :=
  |u - (2*t + inverseCoeffOne/t + inverseCoeffThree/t^3)| ≤ H/t^5

private def modelValue (t : ℝ) := 2*t + inverseCoeffOne/t + inverseCoeffThree/t^3

private theorem model_size {t : ℝ} (ht : 1 ≤ t) : |modelValue t| ≤ 4*t := by
  have ht₀ : 0 < t := by linarith
  have hd {c : ℝ} {k : ℕ} (hc : |c| ≤ 1) : |c/t^k| ≤ 1 := by
    rw [abs_div, abs_of_pos (pow_pos ht₀ _), div_le_one (pow_pos ht₀ _)]
    exact hc.trans (one_le_pow₀ ht)
  have h₁ : |inverseCoeffOne/t| ≤ 1 := by
    simpa using hd (k := 1) (by norm_num [inverseCoeffOne] : |inverseCoeffOne| ≤ 1)
  have h₃ := hd (k := 3) (by norm_num [inverseCoeffThree] : |inverseCoeffThree| ≤ 1)
  unfold modelValue
  calc
    _ ≤ |2*t| + |inverseCoeffOne/t| + |inverseCoeffThree/t^3| :=
      (abs_add_le ..).trans (add_le_add_left (abs_add_le ..) _)
    _ ≤ 4*t := by rw [abs_of_pos (by positivity : 0<2*t)]; linarith

private theorem scaled_error {H a y u : ℝ} (hH : 0 ≤ H) (ha : 1 ≤ a) (hy : 1 ≤ y)
    (hu : InversePhaseApprox H (a*y) u) :
    |u-modelValue (a*y)| ≤ H*a/y^5 ∧ |u| ≤ (4+H)*(a*y) := by
  have ha₀ : 0 < a := by linarith
  have hy₀ : 0 < y := by linarith
  have ht := one_le_mul_of_one_le_of_one_le ha hy
  change |u-modelValue (a*y)| ≤ H/(a*y)^5 at hu
  constructor
  · apply hu.trans
    rw [mul_pow, ← div_div]
    gcongr
    exact (div_le_self hH (one_le_pow₀ ha)).trans (le_mul_of_one_le_right hH ha)
  · have h := (abs_add_le (u-modelValue (a*y)) (modelValue (a*y))).trans
      (add_le_add (hu.trans (div_le_self hH (one_le_pow₀ ht))) (model_size ht))
    rw [sub_add_cancel] at h
    nlinarith [le_mul_of_one_le_right hH ht]

/-- Replacing a pair of values by their models only costs O(ab/y⁴). -/
private theorem pair_error {H a b y u v : ℝ} (hH : 0 ≤ H) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hy : 1 ≤ y)
    (hu : InversePhaseApprox H (a*y) u) (hv : InversePhaseApprox H (b*y) v) :
    |u*v-modelValue (a*y)*modelValue (b*y)| ≤ H*(8+H)*(a*b)/y^4 := by
  have ⟨heu,_⟩ := scaled_error hH ha hy hu
  have ⟨hev,hv'⟩ := scaled_error hH hb hy hv
  have hm := model_size (one_le_mul_of_one_le_of_one_le ha hy)
  have hy₀ : 0 < y := by linarith
  calc
    _ = |(u-modelValue (a*y))*v + modelValue (a*y)*(v-modelValue (b*y))| := by congr 1; ring
    _ ≤ |u-modelValue (a*y)| * |v| + |modelValue (a*y)| * |v-modelValue (b*y)| := by
      simpa only [abs_mul] using abs_add_le ((u-modelValue (a*y))*v) (modelValue (a*y)*(v-modelValue (b*y)))
    _ ≤ (H*a/y^5)*((4+H)*(b*y)) + (4*(a*y))*(H*b/y^5) := by gcongr
    _ = _ := by field_simp; ring

/-- The constant and second-order coefficients of the integer determinant. -/
def detConstant (q r : ℝ) := 2*inverseCoeffOne*(q-1/q)*(r-1/r)

def detCorrection (q r : ℝ) := 2*inverseCoeffThree*(q-1/q^3)*(r-1/r^3)

def detErrorBound (H : ℝ) := 2*H*(8+H)+1

/-- The determinant of the three-term model contains exactly three mixed
products, one for each pair of exponents among 1, -1 and -3. -/
private theorem model_determinant {y q r : ℝ} (hy : 0 < y) (hq : 0 < q) (hr : 0 < r) :
    modelValue y*modelValue ((q*r)*y)-modelValue (q*y)*modelValue (r*y)
      = detConstant q r + detCorrection q r/y^2 +
        inverseCoeffOne*inverseCoeffThree*(1/q-1/q^3)*(1/r-1/r^3)/y^4 := by
  unfold modelValue detConstant detCorrection
  field_simp
  ring

private theorem last_factor {q : ℝ} (hq : 1 ≤ q) : |1/q-1/q^3| ≤ q := by
  have hq₀ : 0 < q := by linarith
  have h₁ := (div_le_one hq₀).mpr hq
  have h₃ := (div_le_one (pow_pos hq₀ 3)).mpr (one_le_pow₀ hq)
  exact abs_le.mpr ⟨by linarith [show 0 ≤ 1/q by positivity], by linarith [show 0 ≤ 1/q^3 by positivity]⟩

/-- The four scale factors 1, q, r and qr give a common leading product.
The remainder after cancellation is uniform even when q and r vary. -/
theorem determinant_approx {H y q r u₀ u₁ u₂ u₃ : ℝ} (hH : 0 ≤ H)
    (hy : 1 ≤ y) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (h₀ : InversePhaseApprox H y u₀) (h₁ : InversePhaseApprox H (q*y) u₁)
    (h₂ : InversePhaseApprox H (r*y) u₂) (h₃ : InversePhaseApprox H ((q*r)*y) u₃) :
    |u₀*u₃-u₁*u₂ - detConstant q r - detCorrection q r/y^2| ≤ detErrorBound H*(q*r)/y^4 := by
  have hqr := one_le_mul_of_one_le_of_one_le hq hr
  have he := pair_error hH (a := 1) le_rfl hqr hy (by simpa using h₀) h₃
  simp only [one_mul] at he
  have hf := pair_error hH hq hr hy h₁ h₂
  have hy₀ : 0 < y := by linarith
  have hd := model_determinant hy₀ (by linarith : 0<q) (by linarith : 0<r)
  let g := inverseCoeffOne*inverseCoeffThree*(1/q-1/q^3)*(1/r-1/r^3)/y^4
  have hg : |g| ≤ (q*r)/y^4 := by
    dsimp [g]; rw [abs_div, abs_of_pos (pow_pos hy₀ _), abs_mul, abs_mul]
    have hab : |inverseCoeffOne*inverseCoeffThree| ≤ 1 := by norm_num [inverseCoeffOne,inverseCoeffThree]
    calc
      _ ≤ 1*q*r/y^4 := by gcongr <;> first | exact last_factor hq | exact last_factor hr
      _ = _ := by ring
  apply abs_le.mpr
  dsimp [g] at hg
  rw [show detErrorBound H*(q*r)/y^4 = 2*(H*(8+H)*(q*r)/y^4) + (q*r)/y^4 by
    unfold detErrorBound; ring]
  obtain ⟨he₁, he₂⟩ := abs_le.mp he
  obtain ⟨hf₁, hf₂⟩ := abs_le.mp hf
  obtain ⟨hg₁, hg₂⟩ := abs_le.mp hg
  constructor <;> linarith

theorem detErrorBound_nonneg {H : ℝ} (hH : 0 ≤ H) : 0 ≤ detErrorBound H := by
  unfold detErrorBound
  positivity

private theorem correction_bounds {q r : ℝ} (hq : 2 ≤ q) (hr : 2 ≤ r) :
    q*r ≤ 32*detCorrection q r ∧ detCorrection q r ≤ q*r := by
  have hb {x : ℝ} (hx : 2 ≤ x) : x/2 ≤ x-1/x^3 ∧ x-1/x^3 ≤ x := by
    have hpos : 0 < x := by linarith
    have hle : 1/x^3 ≤ 1 := (div_le_one (pow_pos hpos 3)).mpr (one_le_pow₀ (by linarith))
    have hnn : 0 ≤ 1/x^3 := by positivity
    constructor <;> linarith
  have hq' := hb hq
  have hr' := hb hr
  have hlow : (q/2)*(r/2) ≤ (q-1/q^3)*(r-1/r^3) := by gcongr <;> linarith
  have hupp : (q-1/q^3)*(r-1/r^3) ≤ q*r := by gcongr <;> linarith
  have hqr : 0 ≤ q*r := by positivity
  unfold detCorrection inverseCoeffThree
  constructor <;> nlinarith

private theorem det_band {L K A z x : ℝ} (hz : 0 < z) (hsmall : 8*A ≤ K*z)
    (hx : |x-L-K/z| ≤ A/z^2) :
    7/8*(K/z) ≤ x-L ∧ x-L ≤ 9/8*(K/z) := by
  have hscale : A/z^2 ≤ (K/z)/8 := by
    field_simp
    linarith
  have h := abs_le.mp (hx.trans hscale)
  constructor <;> linarith

/-- Two integer determinants with the same side lengths cannot both satisfy
the uniform expansion at sufficiently separated base points in a dyadic block. -/
theorem translated_determinants_impossible {C y y' q r : ℝ} {d d' : ℤ}
    (hC : 0 ≤ C) (hy : 1 ≤ y) (hsep : 2*y ≤ y') (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hsmall : 256*C ≤ y^2) (hsize : 2*(q*r) < y^2)
    (hd : |(d : ℝ)-detConstant q r-detCorrection q r/y^2| ≤ C*(q*r)/y^4)
    (hd' : |(d' : ℝ)-detConstant q r-detCorrection q r/y'^2| ≤ C*(q*r)/y'^4) : False := by
  let K := detCorrection q r
  have ⟨hlo, hhi⟩ := correction_bounds hq hr
  change q*r ≤ 32*K at hlo
  change K ≤ q*r at hhi
  have hqr : 0 < q*r := by positivity
  have hK : 0 < K := by linarith
  have hy0 : 0 < y := by linarith
  have hy'0 : 0 < y' := by linarith
  have hwide : 4*y^2 ≤ y'^2 := by nlinarith [sq_le_sq' (by linarith : -y' ≤ 2*y) hsep]
  have hcoeff : 8*(C*(q*r)) ≤ K*y^2 := calc
    _ ≤ 8*(C*(32*K)) := by gcongr
    _ = K*(256*C) := by ring
    _ ≤ _ := by gcongr
  have hcoeff' : 8*(C*(q*r)) ≤ K*y'^2 := hcoeff.trans (by gcongr; nlinarith)
  have hband := det_band (pow_pos hy0 2) hcoeff (by simpa only [← pow_mul] using hd)
  have hband' := det_band (pow_pos hy'0 2) hcoeff' (by simpa only [← pow_mul] using hd')
  have hsep' : K/y'^2 ≤ (K/y^2)/4 := by
    rw [div_div, div_le_div_iff_of_pos_left hK (pow_pos hy'0 _) (by positivity)]
    linarith
  have hratio : K/y^2 < 1/2 :=
    (div_lt_div_iff₀ (pow_pos hy0 _) (by norm_num)).mpr (by linarith)
  have hratio' : 0 < K/y^2 := by positivity
  have hratio'' : 0 < K/y'^2 := by positivity
  change (7/8:ℝ)*(K/y^2) ≤ d-detConstant q r ∧
    (d:ℝ)-detConstant q r ≤ 9/8*(K/y^2) at hband
  change (7/8:ℝ)*(K/y'^2) ≤ d'-detConstant q r ∧
    (d':ℝ)-detConstant q r ≤ 9/8*(K/y'^2) at hband'
  have hlt : d' < d := by exact_mod_cast (show (d' : ℝ) < d by linarith)
  have hlt' : d < d'+1 := by exact_mod_cast (show (d : ℝ) < d'+1 by linarith)
  omega

end Arxiv.«2607.05739»

end
