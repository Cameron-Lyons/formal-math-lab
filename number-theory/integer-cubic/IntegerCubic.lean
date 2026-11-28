module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Partial results for the integer equation z² + y²z + x³ = 2.
These proofs give rational solutions and obstructions to two integer constructions.
-/

public section

namespace IntegerCubic

def Solves {R : Type*} [CommRing R] (x y z : R) : Prop :=
  z ^ 2 + y ^ 2 * z + x ^ 3 = 2

/-- The quadratic matching the branch through (y,z) = (1,1) to second order. -/
theorem contact_identity {R : Type*} [CommRing R] (t u : R) :
    let z := 1 - 6 * t - 3 * t ^ 2
    z ^ 2 + (1 + 9 * t) ^ 2 * z + (t * u) ^ 3 - 2 = t ^ 3 * (u ^ 3 - 234 * t - 504) := by
  dsimp
  ring

/-- The first factor becomes (6n)³ when k = 2028n³ − 2. -/
theorem family_factorization (k : ℚ) :
    let y := 9 * k - 5 / 13
    let z := -78 * k ^ 2 + 12 * k - 2
    2 - z * (z + y ^ 2) = 18 * (k + 2) / 169 * (13 * k - 2) ^ 3 := by
  dsimp
  ring

def family (n : ℕ) : ℤ × ℚ × ℤ :=
  let k : ℤ := 2028 * (n : ℤ) ^ 3 - 2
  (6 * n * (13 * k - 2), ((9 * k : ℤ) : ℚ) - 5 / 13, -78 * k ^ 2 + 12 * k - 2)

theorem family_solves (n : ℕ) :
    Solves ((family n).1 : ℚ) (family n).2.1 ((family n).2.2 : ℚ) := by
  unfold Solves family
  push_cast
  linear_combination -family_factorization (2028 * (n : ℚ) ^ 3 - 2)

theorem family_injective : Function.Injective family := by
  intro a b h
  have hy := congrArg (fun p : ℤ × ℚ × ℤ => p.2.1) h
  dsimp [family] at hy
  push_cast at hy
  have heq : (a : ℚ) ^ 3 = (b : ℚ) ^ 3 := by linarith
  exact_mod_cast (Odd.pow_injective (by decide : Odd 3) heq)

theorem infinitely_many_with_two_integer_coordinates :
    {p : ℤ × ℚ × ℤ | Solves (p.1 : ℚ) p.2.1 (p.2.2 : ℚ)}.Infinite :=
  (Set.infinite_range_of_injective family_injective).mono (by
    rintro _ ⟨n, rfl⟩
    exact family_solves n)

theorem family_y_den (n : ℕ) : (family n).2.1.den = 13 := by
  dsimp [family]
  rw [Rat.intCast_sub_den]
  decide +kernel

theorem family_y_nonintegral (n : ℕ) (y : ℤ) : (family n).2.1 ≠ (y : ℚ) := by
  intro h
  simpa [h] using family_y_den n

theorem integer_examples :
    Solves (-167932 : ℤ) 20983 10505681 ∧ Solves (144360 : ℤ) 10853 (-37445138) := by
  norm_num [Solves]

/-- The complete fiber at x = 0. -/
theorem zero_fiber (y z : ℤ) :
    Solves 0 y z ↔ (y = 1 ∨ y = -1) ∧ (z = 1 ∨ z = -2) := by
  constructor
  · intro hs
    unfold Solves at hs
    have hz : z ∣ 2 := ⟨z + y ^ 2, by linear_combination -hs⟩
    have bound₁ := Int.le_of_dvd (by decide : (0 : ℤ) < 2) hz
    have bound₂ := Int.le_of_dvd (by decide : (0 : ℤ) < 2) (neg_dvd.mpr hz)
    have cases : z = -2 ∨ z = -1 ∨ z = 0 ∨ z = 1 ∨ z = 2 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> norm_num at hs <;> simp <;>
      first | nlinarith [sq_nonneg y] | (apply eq_or_eq_neg_of_sq_eq_sq; nlinarith)
  · rintro ⟨(rfl | rfl), (rfl | rfl)⟩ <;> norm_num [Solves]

/-- The difference between the fourth-degree polynomial and its quadratic
approximation, after removing the third power of the distance from the contact point. -/
private def residual {R : Type*} [CommRing R] (m n y : R) : R :=
  2 * m * (-m ^ 8 + 48 * m ^ 4 * n ^ 4 + 192 * n ^ 8) -
    2 * (3 * m ^ 8 + 48 * m ^ 4 * n ^ 4 - 64 * n ^ 8) * n * y

/-- The residual can never be a cube modulo 13 at an admissible contact point. -/
private theorem local_obstruction : ∀ m n k : ZMod 13, (m ≠ 0 ∨ n ≠ 0) →
    k ^ 2 = m ^ 4 + 8 * n ^ 4 → ∀ y u : ZMod 13, u ^ 3 ≠ residual m n y := by
  decide

/-- At any rational point (m/n,k/n²) of W² = y⁴+8, replace W by its
quadratic Taylor polynomial there. The only possible integer solutions on that
graph have x = 0 and y = m/n. The hypothesis on 13 holds for any fraction in lowest terms. -/
theorem quadratic_contact_obstruction (m n k x y z : ℤ) (hn : n ≠ 0)
    (hprim : ¬ (13 ∣ m ∧ 13 ∣ n)) (hk : k ^ 2 = m ^ 4 + 8 * n ^ 4)
    (hs : Solves x y z)
    (hcontact : n ^ 2 * k ^ 3 * (2 * z + y ^ 2) = k ^ 4 + 2 * m ^ 3 * k ^ 2 * (n * y - m) +
      m ^ 2 * (m ^ 4 + 24 * n ^ 4) * (n * y - m) ^ 2) : x = 0 ∧ n * y = m := by
  have hsq : (2 * z + y ^ 2) ^ 2 = y ^ 4 + 8 - 4 * x ^ 3 := by
    unfold Solves at hs
    linear_combination 4 * hs
  have hid : (k ^ 2 * x) ^ 3 = (n * y - m) ^ 3 * residual m n y := by
    apply mul_left_cancel₀ (a := 4 * n ^ 4) (mul_ne_zero (by decide) (pow_ne_zero _ hn))
    calc
      4 * n ^ 4 * (k ^ 2 * x) ^ 3 =
          k ^ 6 * ((n * y) ^ 4 + 8 * n ^ 4) - (n ^ 2 * k ^ 3 * (2 * z + y ^ 2)) ^ 2 := by
            linear_combination n ^ 4 * k ^ 6 * hsq
      _ = 4 * n ^ 4 * ((n * y - m) ^ 3 * residual m n y) := by
            rw [hcontact, show k ^ 6 = (k ^ 2) ^ 3 by ring, show k ^ 4 = (k ^ 2) ^ 2 by ring, hk]
            unfold residual
            ring
  by_cases h : n * y = m
  · have hk0 : k ≠ 0 := by
      intro heq
      rw [heq] at hk
      nlinarith [sq_nonneg (m ^ 2), sq_pos_of_ne_zero (pow_ne_zero 2 hn)]
    rw [h, sub_self] at hid
    simpa [hk0, h] using hid
  exfalso
  have hd : n * y - m ≠ 0 := sub_ne_zero.mpr h
  obtain ⟨u, hu⟩ := (Int.pow_dvd_pow_iff (by decide : 3 ≠ 0)).mp
    (show (n * y - m) ^ 3 ∣ (k ^ 2 * x) ^ 3 from ⟨_, hid⟩)
  rw [hu, mul_pow] at hid
  have hc := mul_left_cancel₀ (pow_ne_zero 3 hd) hid
  have hp : (m : ZMod 13) ≠ 0 ∨ (n : ZMod 13) ≠ 0 := by
    by_contra! hzero
    exact hprim ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd m 13).mp hzero.1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 13).mp hzero.2⟩
  have hkm : (k : ZMod 13) ^ 2 = (m : ZMod 13) ^ 4 + 8 * (n : ZMod 13) ^ 4 := by
    exact_mod_cast congrArg (fun v : ℤ => (v : ZMod 13)) hk
  apply local_obstruction m n k hp hkm y u
  unfold residual at *
  exact_mod_cast congrArg (fun v : ℤ => (v : ZMod 13)) hc

/-- Neither sign of the quadratic substitution obtained from the tangent at
`(Y,x)=(±10,3)` on `Y²+8=4x³` contains an integral solution. -/
theorem pell_tangents_excluded (x y z : ℤ)
    (hs : Solves x y z)
    (hp : 27 * x = 31 - 5 * y ^ 2 ∨ 27 * x = 31 + 5 * y ^ 2) : False := by
  unfold Solves at hs
  rcases hp with hm | hp
  · have h3 := congrArg (fun m : ℤ => (m : ZMod 3)) hm
    push_cast at h3
    have no : ∀ a b : ZMod 3, 27 * a ≠ 31 - 5 * b ^ 2 := by decide
    exact no x y h3
  · have hx : 2 ≤ x := by nlinarith [sq_nonneg y]
    have identity : 25 * (2 * z + y ^ 2) ^ 2 = (x - 3) ^ 2 * (129 - 100 * x) := by
      linear_combination 100 * hs - (27 * x - 31 + 5 * y ^ 2) * hp
    have hx3 : x = 3 := by
      by_contra h
      have hneg := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr h))
        (show 129 - 100 * x < 0 by omega)
      nlinarith [sq_nonneg (2 * z + y ^ 2)]
    subst x
    have hm := congrArg (fun m : ℤ => (m : ZMod 4)) hp
    push_cast at hm
    exact (by decide : ∀ b : ZMod 4, 27 * 3 ≠ 31 + 5 * b ^ 2) y hm

/-- The finite-field obstruction stops at degree six in x. Taking t to be a
polynomial indeterminate gives an identity of degrees (6, 4, 9). -/
theorem sextic_example {R : Type*} [CommRing R] [CharP R 13] (t : R) :
    let x := t ^ 6 + 6 * t ^ 4 + 5 * t ^ 3 + 5 * t ^ 2 + 2 * t + 5
    let y := 4 * t ^ 4 + 6 * t ^ 2 + 12 * t + 1
    let z := 5 * t ^ 9 + 5 * t ^ 8 + 2 * t ^ 7 + 7 * t ^ 6 + 5 * t ^ 5 +
      3 * t ^ 4 + 7 * t ^ 3 + t ^ 2 + 12 * t + 8
    Solves x y z := by
  dsimp [Solves]
  have h : (13 : R) = 0 := CharP.cast_eq_zero R 13
  grind

end IntegerCubic
