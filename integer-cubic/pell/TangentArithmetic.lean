module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace SmallCubic

/-- If an integral pair lies on the quadratic substitution obtained from a
rational tangent to the Mordell curve, the point of tangency is integral.
Eliminating `v` gives a monic sextic in `u`. Its denominator must divide
the sixth power of its numerator. -/
theorem tangent_parameters_integral (u v : ℚ) (x y : ℤ)
    (hm : v ^ 2 = u ^ 3 - 2)
    (ht : 3 * u ^ 2 * (x : ℚ) = v * (y : ℚ) ^ 2 + u ^ 3 + 4) :
    ∃ U V : ℤ, (U : ℚ) = u ∧ (V : ℚ) = v := by
  have hsextic : (u ^ 3 + 4 - 3 * u ^ 2 * x) ^ 2 = (u ^ 3 - 2) * (y : ℚ) ^ 4 := by
    rw [show u ^ 3 + 4 - 3 * u ^ 2 * x = -(v * (y : ℚ) ^ 2) by linarith, ← hm]
    ring
  let a := u.num
  let d : ℤ := u.den
  have hd : (d : ℚ) ≠ 0 := by
    dsimp [d]
    exact_mod_cast u.den_nz
  have hu : (a : ℚ) / d = u := by simpa [a, d] using u.num_div_den
  rw [← hu] at hsextic
  field_simp [hd] at hsextic
  have hcleared :
      (a ^ 3 + 4 * d ^ 3 - 3 * a ^ 2 * x * d) ^ 2 =
        (a ^ 3 - 2 * d ^ 3) * d ^ 3 * y ^ 4 := by
    exact_mod_cast (show ((a : ℚ) ^ 3 + 4 * (d : ℚ) ^ 3 - 3 * a ^ 2 * x * d) ^ 2 =
      (a ^ 3 - 2 * d ^ 3) * d ^ 3 * y ^ 4 by linear_combination hsextic)
  let l := 4 * d ^ 2 - 3 * a ^ 2 * x
  have hdvd : d ∣ a ^ 6 := by
    refine ⟨(a ^ 3 - 2 * d ^ 3) * d ^ 2 * y ^ 4 - 2 * a ^ 3 * l - d * l ^ 2, ?_⟩
    dsimp [l]
    linear_combination hcleared
  have hnat : u.den ∣ u.num.natAbs ^ 6 := by
    simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hdvd
  have hden : u.den = 1 := (u.reduced.pow_left 6).symm.eq_one_of_dvd hnat
  have hU := Rat.intCast_num_of_den_eq_one hden
  have hv : v ^ 2 = ((u.num ^ 3 - 2 : ℤ) : ℚ) := by
    push_cast
    rwa [hU]
  have hV : v.den ^ 2 = 1 := by simpa using congrArg Rat.den hv
  have hvden : v.den = 1 := by simpa using hV
  exact ⟨_, _, hU, Rat.intCast_num_of_den_eq_one hvden⟩

/-- Neither tangent at the two integer points (3, ±5) produces an integral
solution of the original equation. This branch argument also appears in the
existing formal-math-lab/integer-cubic proof. -/
theorem integral_tangent_branches_excluded (x y z : ℤ)
    (hs : z ^ 2 + y ^ 2 * z + x ^ 3 = 2)
    (ht : 27 * x = 31 - 5 * y ^ 2 ∨ 27 * x = 31 + 5 * y ^ 2) : False := by
  rcases ht with hminus | hplus
  · have hmod := congrArg (fun n : ℤ => (n : ZMod 3)) hminus
    push_cast at hmod
    exact (by decide : ∀ a b : ZMod 3, 27 * a ≠ 31 - 5 * b ^ 2) x y hmod
  · have hx : 2 ≤ x := by nlinarith [sq_nonneg y]
    have hdisc : 25 * (2 * z + y ^ 2) ^ 2 = (x - 3) ^ 2 * (129 - 100 * x) := by
      linear_combination 100 * hs - (27 * x - 31 + 5 * y ^ 2) * hplus
    have hx3 : x = 3 := by
      by_contra h
      have hn := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr h))
        (show 129 - 100 * x < 0 by omega)
      nlinarith [sq_nonneg (2 * z + y ^ 2)]
    subst x
    have hmod := congrArg (fun n : ℤ => (n : ZMod 4)) hplus
    push_cast at hmod
    exact (by decide : ∀ b : ZMod 4, 27 * 3 ≠ 31 + 5 * b ^ 2) y hmod

end SmallCubic
