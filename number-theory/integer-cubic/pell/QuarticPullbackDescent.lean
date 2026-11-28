module

public import QuarticSparse
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

public section

namespace SmallCubic.QuarticPullback

/-- Two rational evaluations of a quadratic with prescribed constant term
recover both of its remaining coefficients over any characteristic-zero field. -/
theorem quadratic_coefficients_descend {K : Type*} [Field K] [CharZero K]
    (k l : K) (r s v w : ℚ) (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s)
    (h₁ : (v : K) = k*r+l*(r:K)^2) (h₂ : (w : K) = k*s+l*(s:K)^2) :
    ∃ a b : ℚ, k = (a : K) ∧ l = (b : K) := by
  let b : ℚ := (v/r-w/s)/(r-s)
  have hr' : (r:K) ≠ 0 := by exact_mod_cast hr
  have hs' : (s:K) ≠ 0 := by exact_mod_cast hs
  have hd : (r:K)-(s:K) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hrs)
  have hb : l = (b:K) := by
    dsimp [b]
    push_cast
    field_simp
    linear_combination (s:K)*(-h₁) + (r:K)*h₂
  refine ⟨v/r-b*r,b,?_,hb⟩
  push_cast
  rw [← hb]
  field_simp
  linear_combination -h₁

/-- The sparse quartic family cannot descend to rational x,y,z even if its
parameter and all five sparse coefficients are initially in a larger field.
Only the two coefficients of z as a quadratic in y−1 need descend. -/
theorem no_rational_sparse_image {K : Type*} [Field K] [CharZero K]
    (a b c f e : K) (hb : b ≠ 0) (hc : c ≠ 0)
    (k l : ℚ) (hf : f = (k:K)*c) (he : e = (l:K)*c^2)
    (h₃ : b^3+2*c+3*f = 0)
    (h₆ : 3*e+(f+c)^2+3*a*b^2 = 0)
    (h₉ : 2*(f+c)*e+c^2*f+3*a^2*b = 0)
    (h₁₂ : e^2+c^2*e+a^3 = 0) : False := by
  let g : ℚ := -3*k-2
  have hbg : b^3 = (g:K)*c := by
    dsimp [g]
    push_cast
    rw [hf] at h₃
    linear_combination h₃
  have hg : g ≠ 0 := by
    intro h
    rw [h] at hbg
    simp [hb] at hbg
  have hg' : (g:K) ≠ 0 := by exact_mod_cast hg
  let A : ℚ := -(3*l+(k+1)^2) / (3*g^2)
  have hA : (A:K)*b^4 = a := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hb)
    rw [mul_assoc, ← pow_add]
    change (A:K)*b^(3*2) = a*b^2
    rw [pow_mul, hbg]
    dsimp [A]
    push_cast
    rw [hf,he] at h₆
    field_simp
    linear_combination -h₆
  have hC : ((1/g : ℚ):K)*b^3 = c := by push_cast; rw [hbg]; field_simp
  have hF : ((k/g : ℚ):K)*b^3 = f := by push_cast; rw [hf,hbg]; field_simp
  have hE : ((l/g^2 : ℚ):K)*b^6 = e := by
    change ((l/g^2 : ℚ):K)*b^(3*2) = e
    rw [pow_mul,hbg,he]
    push_cast
    field_simp
  have ih (t : ℚ) :
      (1+(k/g)*t^3+(l/g^2)*t^6)^2 + (1+(1/g)*t^3)^2*(1+(k/g)*t^3+(l/g^2)*t^6)
        + (1*t+A*t^4)^3 = 2 := by
    apply Rat.cast_injective (α := K)
    push_cast
    let s := (t:K)/b
    have ht : (t:K) = b*s := by dsimp [s]; field_simp
    rw [ht]
    simp only [mul_pow, ← mul_assoc]
    push_cast at hC hF hE
    rw [hC,hF,hE,hA]
    linear_combination s^3*h₃+s^6*h₆+s^9*h₉+s^12*h₁₂
  have hh := QuarticSparse.only_constant A 1 (1/g) (l/g^2) (k/g) ih
  exact one_ne_zero hh.2.1

/-- On such a sparse image, two distinct nonzero rational values of y−1
cannot both give rational z. In particular, it cannot parametrize a rational
curve through the seed with nonconstant rational coordinate functions. -/
theorem no_two_rational_samples {K : Type*} [Field K] [CharZero K]
    (a b c f e : K) (hb : b ≠ 0) (hc : c ≠ 0)
    (h₃ : b^3+2*c+3*f = 0) (h₆ : 3*e+(f+c)^2+3*a*b^2 = 0)
    (h₉ : 2*(f+c)*e+c^2*f+3*a^2*b = 0) (h₁₂ : e^2+c^2*e+a^3 = 0)
    (r s v w : ℚ) (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s)
    (h₁ : (v : K) = (f/c)*r+(e/c^2)*(r:K)^2)
    (h₂ : (w : K) = (f/c)*s+(e/c^2)*(s:K)^2) : False := by
  obtain ⟨k,l,hk,hl⟩ := quadratic_coefficients_descend (f/c) (e/c^2) r s v w hr hs hrs h₁ h₂
  exact no_rational_sparse_image a b c f e hb hc k l
    ((div_eq_iff hc).mp hk) ((div_eq_iff (pow_ne_zero 2 hc)).mp hl) h₃ h₆ h₉ h₁₂

end SmallCubic.QuarticPullback
