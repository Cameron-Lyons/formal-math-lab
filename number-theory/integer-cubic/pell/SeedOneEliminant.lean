module

public import CubicEliminant
public import SeedOneData
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Rational roots of the projection for the cubic substitution through (1,0,1). -/
public section
namespace SmallCubic.SeedOne
open SmallCubic.Eliminant Polynomial

private abbrev value (lc : ℤ) (cs : List ℤ) (w : ℚ) := homog lc w 1 cs

/-- Cleared interpolation identity for the sextic before removing the seed factor. -/
theorem interpolation_identity {R : Type*} [CommRing R] (A H P Q G k : R)
    (hQ : P*Q = 2*k-G^3) :
    P * (A^3*Q + 3*A^2*H*G^2 - 3*A*H^2*G*P + H^3*P^2 - A*k*P) =
      2*k*A^3 - (A*G-H*P)^3 - A*k*P^2 := by
  linear_combination A^3 * hQ

-- Homogeneous certificates include denominators divisible by the test prime.
local macro "projective_certificate" p:num : tactic =>
  `(tactic| (
    let _ : Fact (Nat.Prime $p) := ⟨by decide⟩
    apply no_rat_root $p
    decide +kernel))

private theorem no_general90 (w : ℚ) : value general90Lead general90Low w ≠ 0 := by
  projective_certificate 11
private theorem no_general93 (w : ℚ) : value general93Lead general93Low w ≠ 0 := by
  projective_certificate 5
private theorem no_general105 (w : ℚ) : value general105Lead general105Low w ≠ 0 := by
  projective_certificate 7

private theorem cube_factor (w : ℚ) : 2*w^3-1 ≠ 0 := by
  have h : value 2 [-1, 0, 0] w ≠ 0 := by projective_certificate 7
  simpa [value, homog, pow_succ, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg,
    add_comm] using h

/-- The scalar multiple from the exact projection is irrelevant to its zeros. -/
def projected (w : ℚ) : ℚ :=
  w^330 * (2*w^3-1)^442 * homog general93Lead w 1 general93Low *
    (homog general90Lead w 1 general90Low)^2 * (homog general105Lead w 1 general105Low)^3

theorem projected_zero_iff (w : ℚ) : projected w = 0 ↔ w = 0 := by
  simp [projected, cube_factor w, no_general90 w, no_general93 w, no_general105 w]

private theorem no_s13 (a : ℚ) : value special1d3Lead special1d3Low a ≠ 0 := by
  projective_certificate 7
private theorem no_s118 (a : ℚ) : value special1d18Lead special1d18Low a ≠ 0 := by
  projective_certificate 3
private theorem no_s22 (a : ℚ) : value special2d2Lead special2d2Low a ≠ 0 := by
  projective_certificate 3
private theorem no_s23 (a : ℚ) : value special2d3Lead special2d3Low a ≠ 0 := by
  projective_certificate 7
private theorem no_s26 (a : ℚ) : value special2d6Lead special2d6Low a ≠ 0 := by
  projective_certificate 5
private theorem no_s227 (a : ℚ) : value special2d27Lead special2d27Low a ≠ 0 := by
  projective_certificate 3

def specialOne (a : ℚ) : ℚ := (a-1)^6 * homog special1d3Lead a 1 special1d3Low ^ 4 *
  homog special1d18Lead a 1 special1d18Low

def specialTwo (a : ℚ) : ℚ := (a-2) * homog special2d2Lead a 1 special2d2Low ^ 6 *
  homog special2d3Lead a 1 special2d3Low ^ 4 * homog special2d6Lead a 1 special2d6Low *
  homog special2d27Lead a 1 special2d27Low

theorem special_one_zero_iff (a : ℚ) : specialOne a = 0 ↔ a = 1 := by
  simp [specialOne, no_s13 a, no_s118 a, sub_eq_zero] at *

theorem special_two_zero_iff (a : ℚ) : specialTwo a = 0 ↔ a = 2 := by
  simp [specialTwo, no_s22 a, no_s23 a, no_s26 a, no_s227 a, sub_eq_zero] at *

/-- The only surviving exceptional quintic cannot contain a quadratic squared. -/
theorem special_quintic_exclusion (E : ℚ[X]) (hE : 2 ≤ E.natDegree) :
    ¬ E^2 ∣ X^2 * (X^3-4*X^2+4*X-12) := by
  let K : ℚ[X] := X^2 * (X^3-4*X^2+4*X-12)
  change ¬ E^2 ∣ K
  intro hd
  obtain ⟨Q, hQ⟩ := hd
  have hK : E ∣ K := hQ ▸ dvd_mul_of_dvd_left (dvd_pow_self E (by decide : 2 ≠ 0)) Q
  have hder : E ∣ derivative K := by
    refine ⟨2 * derivative E * Q + E * derivative Q, ?_⟩
    rw [hQ, derivative_mul, derivative_pow, C_eq_natCast]; ring
  have hlin : E ∣ 7008 * (X : ℚ[X]) := by
    have id : (7008 : ℚ[X])*X =
        (-185*X^2+712*X-748) * K + (37*X^3-172*X^2+228*X-292) * derivative K := by
      simp [K, derivative_mul, derivative_sub, derivative_pow, C_ofNat]; ring
    rw [id]
    exact dvd_add (dvd_mul_of_dvd_right hK _) (dvd_mul_of_dvd_right hder _)
  have hn := natDegree_le_of_dvd hlin (by norm_num : (7008 : ℚ[X])*X ≠ 0)
  simp at hn
  omega

end SmallCubic.SeedOne
