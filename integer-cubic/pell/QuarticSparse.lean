module

public import CubicEliminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Test the characteristic-seven pattern shared by the singular quartic orbits.
The rational calculation allows the additional linear term in x. -/

public section
namespace SmallCubic.QuarticSparse
open SmallCubic.Eliminant

private def obstruction (c : ℚ) : ℚ :=
  175616*c^9-1153260*c^8+1366848*c^7+230592*c^6-112896*c^5+
  19548*c^4+4704*c^3+288*c^2+1

private theorem obstruction_ne (c : ℚ) : obstruction c ≠ 0 := by
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let cs : List ℤ := [1,0,288,4704,19548,-112896,230592,1366848,-1153260]
  have cert : ∀ u v : ZMod 11, homog 175616 u v cs = 0 → u=0 ∧ v=0 := by decide +kernel
  have hr := no_rat_root 11 175616 cs cert c
  have heq : homog 175616 c 1 cs = obstruction c := by norm_num [cs, homog, obstruction]; ring
  rwa [← heq]

private theorem normalized_exclusion (a c e f : ℚ)
    (h1 : 3*f+2*c+1=0) (h2 : 3*e+(c+f)^2+3*a=0)
    (h3 : 2*(f+c)*e+c^2*f+3*a^2=0) (h4 : e^2+c^2*e+a^3=0) : False := by
  have hf : f = -(2*c+1)/3 := by linarith
  have he : e = -a-(c-1)^2/27 := by rw [hf] at h2; linear_combination h2/3
  rw [he,hf] at h3
  rw [he] at h4
  let p0 := -56*c^3-21*c^2-6*c+2
  have hp : 243*a^2+54*(1-c)*a+p0=0 := by dsimp [p0]; linear_combination 81*h3
  have hq : 729*a^3+729*a^2+(-675*c^2-108*c+54)*a-26*c^4+50*c^3-21*c^2-4*c+1=0 := by
    linear_combination 729*h4
  let l := 504*c^3-1728*c^2-234
  let s := 34*c^4+584*c^3+96*c^2+26*c-11
  have hr : l*a+s=0 := by dsimp [l,s,p0] at *; linear_combination 3*hq-(9*a+2*c+7)*hp
  apply obstruction_ne c
  unfold obstruction
  dsimp [l,s,p0] at hp hr ⊢
  linear_combination ((243*(l*a-s)+54*(1-c)*l)*hr-l^2*hp)/81

private theorem coefficients (a b c e f : ℚ)
    (h : ∀ t : ℚ, (1+f*t^3+e*t^6)^2 + (1+c*t^3)^2*(1+f*t^3+e*t^6) +
      (b*t+a*t^4)^3=2) :
    3*f+2*c+b^3=0 ∧ 3*e+(c+f)^2+3*b^2*a=0 ∧
    2*(f+c)*e+c^2*f+3*b*a^2=0 ∧ e^2+c^2*e+a^3=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination (512*(h 1 - h (-1)) - (h 2 - h (-2)))/1008
  · linear_combination (4096*(h 1 + h (-1)) - (h 2 + h (-2)))/8064
  · linear_combination ((h 2 - h (-2))-8*(h 1-h (-1)))/1008
  · linear_combination ((h 2 + h (-2))-64*(h 1+h (-1)))/8064

/-- The sparse (4,3,6) polynomial substitution yields only the constant seed over ℚ. -/
theorem only_constant (a b c e f : ℚ)
    (h : ∀ t : ℚ, (1+f*t^3+e*t^6)^2 + (1+c*t^3)^2*(1+f*t^3+e*t^6) +
      (b*t+a*t^4)^3=2) : a=0 ∧ b=0 ∧ c=0 ∧ e=0 ∧ f=0 := by
  by_cases hb : b=0
  · subst b
    obtain ⟨h1,h2,h3,h4⟩ := coefficients a 0 c e f h
    have hf : f = -2*c/3 := by linarith
    have he : e = -c^2/27 := by rw [hf] at h2; linear_combination h2/3
    have hc : c^3=0 := by rw [he,hf] at h3; linear_combination (-81/56)*h3
    have hc' : c=0 := by simpa using hc
    subst c
    simp at he hf
    subst e
    subst f
    simpa using h4
  · have h' : ∀ t : ℚ,
        (1+(f/b^3)*t^3+(e/b^6)*t^6)^2 +
        (1+(c/b^3)*t^3)^2*(1+(f/b^3)*t^3+(e/b^6)*t^6) +
        (1*t+(a/b^4)*t^4)^3=2 := by
      intro t
      convert h (t/b) using 1
      field_simp [hb]
    obtain ⟨h1,h2,h3,h4⟩ := coefficients (a/b^4) 1 (c/b^3) (e/b^6) (f/b^3) h'
    simp only [one_pow, mul_one] at h1 h2 h3
    exact False.elim (normalized_exclusion _ _ _ _ h1 h2 h3 h4)

end SmallCubic.QuarticSparse
