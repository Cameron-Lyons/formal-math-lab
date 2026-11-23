import BlockLCM.Defect
import BlockLCM.Sextic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Erdos677

open Finset

/-- The product of five consecutive integers with center `x`. -/
def fiveProduct (x : ℤ) : ℤ := x * (x^2 - 1) * (x^2 - 4)

/-- The possible reduced coefficients in `a * fiveProduct Y = b * fiveProduct X`
when the later center is `Y`. -/
def fiveRatios : Finset (ℕ × ℕ) :=
  {(1, 2), (1, 3), (1, 4), (1, 6), (1, 12), (2, 3), (3, 4)}

private def reducedPair (a b : ℕ) : ℕ × ℕ := (a / a.gcd b, b / a.gcd b)

/-- The coefficient pair attached to these two starts, computable modulo twelve. -/
def fiveRatio (n m : ℕ) : ℕ × ℕ := reducedPair (fiveDefect n) (fiveDefect m)

private abbrev DefectRatioSpec (a b : ℕ) : Prop :=
  let p := reducedPair a b
  0 < p.1 * b ∧ p.1 * b = p.2 * a ∧ (a < b → p ∈ fiveRatios)

private theorem defect_ratio_facts (n m : ℕ) : DefectRatioSpec (fiveDefect n) (fiveDefect m) :=
  of_five_defect_residues (P := DefectRatioSpec) (by decide) n m

private theorem fiveProduct_at_center (n : ℕ) :
    fiveProduct (n + 3) = (fiveBlockProduct n : ℤ) := by
  simp [fiveProduct, fiveBlockProduct]
  ring

/-- For the coefficients determined by the starting residues, the quintic
equation characterizes equality of LCMs in both directions. -/
theorem five_collision_iff_product (n m : ℕ) :
    lcmInterval m 5 = lcmInterval n 5 ↔
    ((fiveRatio n m).1 : ℤ) * fiveProduct (m + 3) =
    ((fiveRatio n m).2 : ℤ) * fiveProduct (n + 3) := by
  obtain ⟨hpos, hcoeff, _⟩ := defect_ratio_facts n m
  rw [fiveProduct_at_center, fiveProduct_at_center]
  norm_cast
  rw [← lcmInterval_five_mul_defect, ← lcmInterval_five_mul_defect,
    mul_left_comm (fiveRatio n m).1, mul_left_comm (fiveRatio n m).2, fiveRatio, ← hcoeff]
  exact (Nat.mul_left_inj hpos.ne').symm

/-- The coefficient pair of a collision is one of the seven reduced pairs. -/
theorem fiveRatio_mem_of_collision {n m : ℕ} (hnm : n < m)
    (heq : lcmInterval m 5 = lcmInterval n 5) : fiveRatio n m ∈ fiveRatios := by
  apply (defect_ratio_facts n m).2.2
  exact lt_of_not_ge fun h => (lcmInterval_five_strict_of_defect_le hnm h).ne' heq

/-- The rational center ratio of a collision is the first coordinate of a
point on one of seven explicitly specified sextics. -/
theorem five_collision_sextic {m n : ℕ} (hnm : n < m)
    (heq : lcmInterval m 5 = lcmInterval n 5) :
    let t := ((m : ℚ) + 3) / (n + 3)
    ∃ p ∈ fiveRatios, ∃ z : ℚ, z^2 =
      25 * ((p.1 : ℚ) * t^3 - p.2)^2 -
      16 * ((p.1 : ℚ) * t^5 - p.2) * ((p.1 : ℚ) * t - p.2) := by
  have hprod := (five_collision_iff_product n m).mp heq
  refine ⟨fiveRatio n m, fiveRatio_mem_of_collision hnm heq, ?_⟩
  apply five_ratio_sextic (X := (n : ℚ) + 3) (Y := (m : ℚ) + 3) (by positivity)
  unfold fiveProduct at hprod
  exact_mod_cast hprod

end Erdos677
