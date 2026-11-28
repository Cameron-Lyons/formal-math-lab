module

public import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace SmallCubic.OneMarkLocal

open Polynomial

/-- Hensel lifting at 1 solves 3a³ = 7 in the 2-adic integers. -/
theorem local_two_root : ∃ a : ℤ_[2], 3 * a^3 = 7 := by
  let F : Polynomial ℤ := C 3 * X^3 - C 7
  have h₁ : F.aeval (1 : ℤ_[2]) = -4 := by
    simp only [F, map_sub, map_mul, map_pow, aeval_C, aeval_X]
    norm_num
  have h₂ : F.derivative.aeval (1 : ℤ_[2]) = 9 := by
    simp only [F, derivative_sub, derivative_C_mul, derivative_X_pow, derivative_C, sub_zero, map_mul, map_pow, aeval_C, aeval_X]
    norm_num
  have hlt : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖^2 := by
    rw [h₁, h₂, norm_neg]
    have hv : ‖(9 : ℤ_[2])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 2 9)
    rw [hv, one_pow]
    exact PadicInt.norm_natCast_lt_one_iff.mpr (by decide : 2 ∣ 4)
  obtain ⟨a,ha,-⟩ := hensels_lemma hlt
  refine ⟨a, sub_eq_zero.mp ?_⟩
  simp only [F, map_sub, map_mul, map_pow, aeval_C, aeval_X] at ha
  norm_num at ha
  exact ha

variable {K : Type*} [Field K] [CharZero K]

def ordY (s : K) : K := (108*s^3-239)/13
def ordX (s : K) : K := (2/3)*s*(ordY s-1)
def ordZ (s : K) : K := (44 - (ordY s)^2 - 16*ordY s)/27

theorem local_identity (s : K) : (ordZ s)^2 + (ordY s)^2*(ordZ s) + (ordX s)^3 = 2 := by
  unfold ordZ ordX ordY
  ring

theorem local_seed (a : K) (ha : 3*a^3=7) :
    ordX a=0 ∧ ordY a=1 ∧ ordZ a=1 := by
  have hy : ordY a = 1 := by
    unfold ordY
    field_simp
    linear_combination 36*ha
  simp [ordX, ordZ, hy]
  norm_num

theorem second_x (a : K) (ha : 3*a^3=7) : ordX (a+1) ≠ 0 := by
  intro h
  unfold ordX ordY at h
  have ab : a+1 ≠ 0 := by
    intro hb
    have hv : a = -1 := by linear_combination hb
    rw [hv] at ha
    norm_num at ha
  have hv := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) ab)
  field_simp at hv
  have hq : 3*a^2+3*a+1 = 0 := by linear_combination hv/108-ha/3
  have hl : a=3 := by linear_combination (ha-(a-1)*hq)/2
  rw [hl] at ha
  norm_num at ha

/-- These degree-(4,3,6) polynomials in the Pell variable v work over ℚ₂.
At (u,v)=(1,0) and (2,1) their first coordinates are different. -/
theorem local_two_polynomials : ∃ a : ℚ_[2],
    (ordX a = 0 ∧ ordY a = 1 ∧ ordZ a = 1) ∧ ordX (a+1) ≠ 0 ∧
    ∀ v : ℚ_[2], (ordZ (a+v))^2 + (ordY (a+v))^2*(ordZ (a+v)) +
      (ordX (a+v))^3 = 2 := by
  obtain ⟨a,ha⟩ := local_two_root
  have h : 3*(a : ℚ_[2])^3=7 := by
    have hc := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) ha
    exact hc
  exact ⟨a, local_seed _ h, second_x _ h, fun v => local_identity _⟩

end SmallCubic.OneMarkLocal
