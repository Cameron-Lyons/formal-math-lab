module

public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The auxiliary equation at the lost quartic pole, over the residue field at 13. -/
public section
namespace SmallCubic.QuarticReflection

abbrev F := ZMod 13
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

private theorem quartic_coefficients (a b c d e : F)
    (h : ∀ t : F, a*t^4 + b*t^3 + c*t^2 + d*t + e = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  have he := h 0
  simp at he
  subst e
  have ha : (24:F)*a = 0 := by
    linear_combination h 2 + h (-2) - 4 * h 1 - 4 * h (-1)
  have hb : (12:F)*b = 0 := by
    linear_combination h 2 - h (-2) - 2 * h 1 + 2 * h (-1)
  have ha' := (mul_eq_zero.mp ha).resolve_left (by decide)
  have hb' := (mul_eq_zero.mp hb).resolve_left (by decide)
  subst a; subst b
  have hc : (2:F)*c=0 := by linear_combination h 1 + h (-1)
  have hc' := (mul_eq_zero.mp hc).resolve_left (by decide)
  subst c
  simpa using h 1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem no_affine_case : ∀ a g k c : F, k ≠ 0 →
    let d := (k^2 - 12*a)/4
    let e := k^2*g
    ¬ (d^2=6*k^2*g^2+12*a^2 ∧ 2*d*e=4*k^2*g^3 ∧ e^2=8*c^6+k^2*g^4-4*a^3) := by
  decide +kernel

private theorem sixth_and_fourth : ∀ k g c : F, k ≠ 0 →
    8*c^6 + k^2*g^4=0 → c=0 ∧ g=0 := by decide +kernel

/-- The nonzero quadratic and cubic leading coefficients determine the scaling. -/
theorem scale_leading : ∀ a w : F, a ≠ 0 → w^2 = -4*a^3 →
    ∃ s : F, s ≠ 0 ∧ a = -s^2 ∧ w=2*s^3 := by decide +kernel

/-- With centered quadratic abscissa and the cubic leading term normalized,
the residual identity forces a pure square/cube monomial degeneration. -/
theorem normalized_zoom (a d e m g k c : F) (hk : k ≠ 0)
    (h : ∀ t : F, (2*t^3 + d*t + e)^2 =
      8*c^6 + k^2*(m*t+g)^4 - 4*(-t^2+a)^3) :
    a=0 ∧ d=0 ∧ e=0 ∧ m=0 ∧ g=0 ∧ c=0 := by
  have co := quartic_coefficients
    (4*d - k^2*m^4 + 12*a) (4*e - 4*k^2*m^3*g)
    (d^2-6*k^2*m^2*g^2-12*a^2) (2*d*e-4*k^2*m*g^3)
    (e^2-8*c^6-k^2*g^4+4*a^3) (fun t => by linear_combination h t)
  obtain ⟨h4,h3,h2,h1,h0⟩ := co
  by_cases hm : m=0
  · subst m
    have he : e=0 := (mul_eq_zero.mp (show (4:F)*e=0 by simpa using h3)).resolve_left (by decide)
    subst e
    have hd : d = -3*a := by
      apply mul_left_cancel₀ (show (4:F) ≠ 0 by decide)
      linear_combination h4
    subst d
    have ha : a=0 := by
      apply eq_zero_of_pow_eq_zero (n := 2)
      apply (mul_eq_zero.mp (show (-3:F)*a^2=0 by linear_combination h2)).resolve_left (by decide)
    subst a
    obtain ⟨hc,hg⟩ := sixth_and_fourth k g c hk (by linear_combination -h0)
    simp [hc,hg]
  · exfalso
    let K := k*m^2
    let G := g/m
    have hG : m*G = g := by dsimp [G]; field_simp
    rw [← hG] at h3 h2 h1 h0
    have hd : (K^2-12*a)/4 = d := by
      rw [div_eq_iff (by decide : (4:F) ≠ 0)]
      dsimp [K]; linear_combination -h4
    have he : K^2*G = e := by
      apply mul_left_cancel₀ (show (4:F) ≠ 0 by decide)
      dsimp [K]; linear_combination -h3
    apply no_affine_case a G K c (mul_ne_zero hk (pow_ne_zero _ hm))
    rw [hd,he]
    dsimp [K]
    exact ⟨by linear_combination h2, by linear_combination h1, by linear_combination h0⟩

end SmallCubic.QuarticReflection
