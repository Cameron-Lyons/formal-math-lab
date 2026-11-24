module

public import AffineTangent
public import QuarticRoots
public import Fibers
public import CubicRoots
public import MordellDescent
public import TangentArithmetic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Searching for Pell families on z² + y²z + x³ = 2

Setting w = 2z + y² turns the equation into w² = y⁴ + 8 − 4x³.
A repeated factor in the right-hand side could be removed as a square. The
two main theorems below exclude this route for every rational graph of the
form x = ay + b or x = ay² + b that contains an integral solution.

The auxiliary modules prove the necessary descent on v² = u³ − 2 and the
equivalence of infinitude with unbounded |x|. The accompanying Python search
also tests x = (Ay² + By + C)/D with bounded coefficients.

The infinitude question is equation (4) of Grechuk, arXiv:2404.08518v11.
-/
public section

namespace SmallCubic

def Solves (x y z : ℤ) : Prop := z ^ 2 + y ^ 2 * z + x ^ 3 = 2

/-- Completing the square is reversible for a given integer triple. -/
theorem solves_iff_discriminant (x y z : ℤ) :
    Solves x y z ↔ (2 * z + y ^ 2) ^ 2 = y ^ 4 + 8 - 4 * x ^ 3 := by
  unfold Solves
  constructor <;> intro h
  · linear_combination 4 * h
  · nlinarith only [h]

/-- A square discriminant already has the parity required to recover an integral z. -/
theorem exists_z_iff_square (x y : ℤ) :
    (∃ z, Solves x y z) ↔ ∃ w : ℤ, w ^ 2 = y ^ 4 + 8 - 4 * x ^ 3 := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨_, (solves_iff_discriminant ..).mp hz⟩
  · rintro ⟨w, hw⟩
    have hm := congrArg (fun n : ℤ => (n : ZMod 2)) hw
    push_cast at hm
    have parity : ∀ u v k : ZMod 2, u ^ 2 = v ^ 4 + 8 - 4 * k ^ 3 → u - v ^ 2 = 0 := by decide
    have he : ((w - y ^ 2 : ℤ) : ZMod 2) = 0 := by
      push_cast
      exact parity w y x hm
    obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp he
    exact ⟨z, (solves_iff_discriminant ..).mpr (by rwa [show 2 * z + y ^ 2 = w by omega])⟩

/-- The repeated factors for the two candidates returned by the quadratic search.
Here s stands for y². -/
theorem tangent_factorizations (s : ℤ) :
    27 ^ 3 * (s ^ 2 + 8) - 4 * (31 - 5 * s) ^ 3 =
      (s + 10) ^ 2 * (500 * s + 383) ∧
    27 ^ 3 * (s ^ 2 + 8) - 4 * (31 + 5 * s) ^ 3 =
      (s - 10) ^ 2 * (383 - 500 * s) := by
  constructor <;> ring

/-- The explicit substitution behind the real Pell branch, with denominators
cleared. The multiplier (y²+10)² is strictly positive over the rationals. -/
theorem pell_substitution (y t : ℚ) :
    let x := (31 - 5*y^2)/27
    let z := ((y^2+10)*t/27 - y^2)/2
    4 * 27^3 * (z^2 + y^2*z + x^3 - 2) =
      (y^2+10)^2 * (27*t^2 - 500*y^2 - 383) := by
  dsimp
  ring

/-- For integral y even a rational Pell seed is impossible. The square of 9t
would be an integer congruent to 3 or 6 modulo 9. -/
theorem no_rational_pell_seed (t : ℚ) (y : ℤ) : 27*t^2 - 500*(y : ℚ)^2 ≠ 383 := by
  intro h
  let n := 9*t
  have hn : n^2 = ((1500*y^2 + 1149 : ℤ) : ℚ) := by
    dsimp [n]; push_cast; linear_combination 3*h
  have hd : n.den^2 = 1 := by simpa only [Rat.den_pow, Rat.den_intCast] using congrArg Rat.den hn
  have hi := Rat.intCast_num_of_den_eq_one (show n.den = 1 by simpa using hd)
  rw [← hi] at hn
  have hz : n.num^2 = 1500*y^2 + 1149 := by exact_mod_cast hn
  have hm := congrArg (fun m : ℤ => (m : ZMod 9)) hz
  push_cast at hm
  exact (by decide : ∀ u v : ZMod 9, u^2 ≠ 1500*v^2 + 1149) _ _ hm

/-- A rational multiple root of the cubic in s = y² would give an integral
tangent point on the Mordell curve. Its two possibilities are both excluded. -/
theorem no_rational_contact (a b r : ℚ) (x y z : ℤ) (hs : Solves x y z)
    (hx : (x : ℚ) = a * (y : ℚ) ^ 2 + b)
    (hf : r ^ 2 + 8 - 4 * (a * r + b) ^ 3 = 0)
    (hf' : 2 * r - 12 * a * (a * r + b) ^ 2 = 0) : False := by
  let u := a * r + b
  let v := r / 2
  have hE : v ^ 2 = u ^ 3 - 2 := by dsimp [u, v]; linear_combination (1/4 : ℚ) * hf
  have hv : v = 3 * a * u ^ 2 := by dsimp [u, v]; linear_combination (1/4 : ℚ) * hf'
  have hx' : (x : ℚ) = a * ((y : ℚ) ^ 2 - 2 * v) + u := by rw [hx]; dsimp [u, v]; ring
  have ht : 3 * u ^ 2 * (x : ℚ) = v * (y : ℚ) ^ 2 + u ^ 3 + 4 := by
    rw [hx']
    linear_combination -((y : ℚ) ^ 2 - 2 * v) * hv - 2 * hE
  obtain ⟨U, V, hU, hV⟩ := tangent_parameters_integral u v x y hE ht
  rw [← hU, ← hV] at hE ht
  have hM : V ^ 2 + 2 = U ^ 3 := by exact_mod_cast (show (V : ℚ) ^ 2 + 2 = U ^ 3 by linarith)
  obtain ⟨rfl, hV'⟩ := mordell_classification U V hM
  apply integral_tangent_branches_excluded x y z hs
  rcases hV' with rfl | rfl
  · right
    exact_mod_cast (show 27 * (x : ℚ) = 31 + 5 * (y : ℚ) ^ 2 by push_cast at ht; linarith)
  · left
    exact_mod_cast (show 27 * (x : ℚ) = 31 - 5 * (y : ℚ) ^ 2 by push_cast at ht; linarith)

private theorem two_not_rational_cube (q : ℚ) : q ^ 3 ≠ 2 := by
  intro h
  have hd : q.den ^ 3 = 1 := by simpa using congrArg Rat.den h
  have hq := Rat.intCast_num_of_den_eq_one (show q.den = 1 by simpa using hd)
  rw [← hq] at h
  have hz : q.num ^ 3 = (2 : ℤ) := by exact_mod_cast h
  have hm := congrArg (fun n : ℤ => (n : ZMod 7)) hz
  push_cast at hm
  exact (by decide : ∀ n : ZMod 7, n ^ 3 ≠ 2) _ hm

/-- For any even quadratic graph x = a y² + b containing an integer solution,
the sextic discriminant and its derivative have no common root, even over an
extension field. Thus it has no repeated factor to remove for a Pell reduction. -/
theorem even_quadratic_no_repeated_root
    {K : Type*} [Field K] [CharZero K] (a b : ℚ) (ha : a ≠ 0)
    (x y z : ℤ) (hs : Solves x y z) (hx : (x : ℚ) = a * (y : ℚ) ^ 2 + b) (t : K) :
    ¬ (t ^ 4 + 8 - 4 * ((a : K) * t ^ 2 + b) ^ 3 = 0 ∧
       4 * t ^ 3 - 24 * (a : K) * t * (a * t ^ 2 + b) ^ 2 = 0) := by
  rintro ⟨hf, hf'⟩
  have h0 : t ≠ 0 := by
    rintro rfl
    have hb : (b : K) ^ 3 = 2 := by linear_combination (-1/4 : K) * hf
    exact two_not_rational_cube b (by exact_mod_cast hb)
  have hder : 2 * t ^ 2 - 12 * (a : K) * (a * t ^ 2 + b) ^ 2 = 0 := by
    have hprod : t * (2 * t ^ 2 - 12 * (a : K) * (a * t ^ 2 + b) ^ 2) = 0 := by
      linear_combination (1/2 : K) * hf'
    exact (mul_eq_zero.mp hprod).resolve_left h0
  obtain ⟨r, _, hr, hr'⟩ := rational_multiple_root_of_cubic
    (-4 * a ^ 3) (1 - 12 * a ^ 2 * b) (-12 * a * b ^ 2) (8 - 4 * b ^ 3)
    (by simp [ha]) (t ^ 2) (by push_cast; linear_combination hf) (by push_cast; linear_combination hder)
  exact no_rational_contact a b r x y z hs hx (by linear_combination hr) (by linear_combination hr')

/-- The analogous quartic for an affine graph cannot have a multiple root.
It suffices that the graph passes through an integer pair (x,y). -/
theorem affine_no_repeated_root {K : Type*} [Field K] [CharZero K]
    (a b : ℚ) (ha : a ≠ 0) (x y : ℤ) (hx : (x : ℚ) = a * y + b) (t : K) :
    ¬ (t ^ 4 + 8 - 4 * ((a : K) * t + b) ^ 3 = 0 ∧
       4 * t ^ 3 - 12 * (a : K) * (a * t + b) ^ 2 = 0) := by
  rintro ⟨hf, hf'⟩
  rcases quartic_repeated_root K (-4*a^3) (-12*a^2*b) (-12*a*b^2) (8-4*b^3) t
      (by push_cast; linear_combination hf) (by push_cast; linear_combination hf') with
      ⟨r, hr, hr'⟩ | ⟨p, q, h⟩
  · exact affine_no_rational_tangent a b r (a*r+b) x y hx rfl
      (by linear_combination hr) (by linear_combination (1/4 : ℚ) * hr')
  · have hp : 2*p = -4*a^3 := by
      linear_combination (-1/12 : ℚ) * (h 2 - h (-2) - 2 * h 1 + 2 * h (-1))
    have hp0 : p ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hp
      exact (mul_ne_zero (by decide : (-4 : ℚ) ≠ 0) (pow_ne_zero _ ha)) hp.symm
    let s := -q / p
    have hz : s^2+p*s+q = s^2 := by dsimp [s]; field_simp; ring
    have h' := h s
    rw [hz] at h'
    exact two_not_rational_cube (a*s+b) (by linear_combination (-1/4 : ℚ) * h')

/-- Independently checkable integral witnesses, with their x values in increasing order. -/
theorem three_integer_solutions :
    Solves (-5547568) 22374985 341022 ∧
    Solves (-3835747) 26512930 80285 ∧
    Solves 22745 71792 (-2283) ∧
    (-5547568 : ℤ) < -3835747 ∧ (-3835747 : ℤ) < 22745 := by
  unfold Solves
  decide

end SmallCubic
