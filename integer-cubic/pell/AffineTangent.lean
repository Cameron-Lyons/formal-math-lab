module

public import MordellDescent
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

public section

namespace SmallCubic

/-- A rational root of the monic degree-twelve equation for an affine tangent
has denominator one. -/
private theorem affine_parameter_integral (u : ℚ) (x y : ℤ)
    (h : (3 * u ^ 2 * x + u ^ 3 - 8) ^ 4 = (4 * u ^ 3 - 8) ^ 3 * y ^ 4) :
    (u.num : ℚ) = u := by
  let n := u.num
  let d : ℤ := u.den
  have hd : (d : ℚ) ≠ 0 := by dsimp [d]; exact_mod_cast u.den_nz
  have hu : (n : ℚ) / d = u := by simpa [n, d] using u.num_div_den
  rw [← hu] at h
  field_simp [hd] at h
  have hz :
      (3 * n ^ 2 * x * d + n ^ 3 - 8 * d ^ 3) ^ 4 =
      (4 * n ^ 3 - 8 * d ^ 3) ^ 3 * y ^ 4 * d ^ 3 := by
    exact_mod_cast (show (3 * (n : ℚ) ^ 2 * x * d + n ^ 3 - 8 * d ^ 3) ^ 4 =
      (4 * n ^ 3 - 8 * d ^ 3) ^ 3 * y ^ 4 * d ^ 3 by linear_combination h)
  have hm := congrArg (fun z : ℤ => (z : ZMod u.den)) hz
  push_cast at hm
  have hd0 : (d : ZMod u.den) = 0 := by simp [d]
  have hzero : (n : ZMod u.den) ^ 12 = 0 := by simpa [hd0, ← pow_mul] using hm
  have hdvd : (u.den : ℤ) ∣ n ^ 12 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ u.den).mp
    push_cast
    exact hzero
  have hnat : u.den ∣ u.num.natAbs ^ 12 := by
    simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hdvd
  exact Rat.intCast_num_of_den_eq_one ((u.reduced.pow_left 12).symm.eq_one_of_dvd hnat)

/-- A rational affine line through an integral pair cannot be tangent to
`r⁴ = 4u³ − 8` at a rational point. -/
theorem affine_no_rational_tangent (a b r u : ℚ) (x y : ℤ)
    (hx : (x : ℚ) = a * y + b) (hu : u = a * r + b)
    (hf : r ^ 4 = 4 * u ^ 3 - 8) (hf' : r ^ 3 = 3 * a * u ^ 2) : False := by
  have hcontact : 3 * u ^ 2 * x + u ^ 3 - 8 = r ^ 3 * y := by
    linear_combination 3 * u ^ 2 * hx - 3 * u ^ 2 * hu - ((y : ℚ) - r) * hf' - hf
  have h12 : (3 * u ^ 2 * x + u ^ 3 - 8) ^ 4 = (4 * u ^ 3 - 8) ^ 3 * y ^ 4 := by
    rw [hcontact, ← hf]
    ring
  have hU := affine_parameter_integral u x y h12
  let v := r ^ 2 / 2
  have hM : v ^ 2 = (((u.num ^ 3 - 2 : ℤ) : ℚ)) := by
    push_cast
    rw [hU]
    dsimp [v]
    linear_combination (1/4 : ℚ) * hf
  have hVden : v.den ^ 2 = 1 := by simpa using congrArg Rat.den hM
  have hV := Rat.intCast_num_of_den_eq_one (show v.den = 1 by simpa using hVden)
  rw [← hV] at hM
  have hm : v.num ^ 2 = u.num ^ 3 - 2 := by exact_mod_cast hM
  have h3 := (mordell_classification u.num v.num (by omega)).1
  have hu3 : u = 3 := by rw [← hU, h3]; norm_num
  rw [hu3] at hf
  norm_num at hf
  have hrden : r.den ^ 4 = 1 := by simpa using congrArg Rat.den hf
  have hR := Rat.intCast_num_of_den_eq_one (show r.den = 1 by simpa using hrden)
  rw [← hR] at hf
  have hz : r.num ^ 4 = (100 : ℤ) := by exact_mod_cast hf
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) hz
  push_cast at hmod
  exact (by decide : ∀ n : ZMod 16, n ^ 4 ≠ 100) _ hmod

end SmallCubic
