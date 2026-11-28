module

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Euclidean division in the quadratic integer ring ℤ[√−2]. The norm is
`a² + 2b²`. Rounding both coordinates of a quotient leaves squared errors
at most one quarter, so the remainder has strictly smaller norm. -/

public section

namespace SmallCubic

namespace SqrtNegTwo

abbrev R := Zsqrtd (-2)
open Zsqrtd

def quotient (a b : R) : R :=
  let c := a * star b
  ⟨c.re.bdiv b.norm.natAbs, c.im.bdiv b.norm.natAbs⟩

private theorem bmodSquareLe (a : ℤ) (n : ℕ) (hn : 0 < n) :
    4 * (a.bmod n) ^ 2 ≤ (n : ℤ) ^ 2 := by
  have hl := Int.le_bmod (x := a) hn
  have hu := Int.bmod_lt (x := a) hn
  have hl' : 0 ≤ (n : ℤ) + 2 * a.bmod n := by omega
  have hu' : 0 ≤ (n : ℤ) - 2 * a.bmod n := by omega
  nlinarith [mul_nonneg hl' hu']

theorem remainderNormLt (a b : R) (hb : b ≠ 0) :
    (a - b * quotient a b).norm.natAbs < b.norm.natAbs := by
  let c := a * star b
  let n := b.norm.natAbs
  have bn : (n : ℤ) = b.norm := Int.natAbs_of_nonneg (norm_nonneg (by decide) b)
  have hn : 0 < n := by
    have := (norm_eq_zero_iff (by decide : (-2 : ℤ) < 0) b).not.mpr hb
    have := norm_nonneg (by decide : (-2 : ℤ) ≤ 0) b
    omega
  have scaledRemainder : (a - b * quotient a b) * star b =
      (⟨c.re.bmod n, c.im.bmod n⟩ : R) := by
    rw [sub_mul, mul_right_comm b, ← norm_eq_mul_conj, ← bn]
    ext <;> simp [quotient, c, n, Int.bmod_eq_self_sub_mul_bdiv]
  have normIdentity := congrArg norm scaledRemainder
  rw [norm_mul, norm_conj] at normIdentity
  change (a - b * quotient a b).norm * b.norm =
    c.re.bmod n * c.re.bmod n - (-2) * c.im.bmod n * c.im.bmod n at normIdentity
  have hn2 : 0 < (n : ℤ) ^ 2 := by positivity
  have hlt : (a - b * quotient a b).norm * (n : ℤ) < (n : ℤ) * n := by
    rw [← bn] at normIdentity
    nlinarith [bmodSquareLe c.re n hn, bmodSquareLe c.im n hn]
  have := lt_of_mul_lt_mul_right hlt (by positivity)
  have := Int.natAbs_of_nonneg (norm_nonneg (by decide : (-2 : ℤ) ≤ 0)
    (a - b * quotient a b))
  omega

end SqrtNegTwo

open SqrtNegTwo Zsqrtd

/-- Euclidean division by the positive definite norm on ℤ[√−2]. -/
@[expose, instance_reducible] def sqrtNegTwoEuclidean : EuclideanDomain (Zsqrtd (-2)) where
  quotient := quotient
  quotient_zero a := by simp [quotient]; rfl
  remainder a b := a - b * quotient a b
  quotient_mul_add_remainder_eq a b := by ring
  r a b := a.norm.natAbs < b.norm.natAbs
  r_wellFounded := (measure (fun a : R => a.norm.natAbs)).wf
  remainder_lt a b hb := remainderNormLt a b hb
  mul_left_not_lt a b hb := by
    change ¬ (a * b).norm.natAbs < a.norm.natAbs
    rw [norm_mul, Int.natAbs_mul]
    have : b.norm.natAbs ≠ 0 := by
      simpa [norm_eq_zero_iff (by decide : (-2 : ℤ) < 0)] using hb
    exact not_lt_of_ge (Nat.le_mul_of_pos_right _ (by omega))

end SmallCubic
