module

public import BlockLCM.Defect
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Erdos677

open Finset

/-- The coefficients of any length-five collision place the ratio of products
in the closed interval from 4/3 to 12. -/
theorem fiveBlockProduct_bounds_of_collision {n m : ℕ} (hnm : n < m)
    (heq : lcmInterval m 5 = lcmInterval n 5) :
    4 * fiveBlockProduct n ≤ 3 * fiveBlockProduct m ∧ fiveBlockProduct m ≤ 12 * fiveBlockProduct n := by
  have hD : fiveDefect n < fiveDefect m := by
    by_contra! h
    exact (lcmInterval_five_strict_of_defect_le hnm h).ne' heq
  obtain ⟨hlo, hhi⟩ := of_five_defect_residues
    (P := fun a b => a < b → 4*a ≤ 3*b ∧ b ≤ 12*a) (by decide) n m hD
  rw [← lcmInterval_five_mul_defect, ← lcmInterval_five_mul_defect, heq]
  constructor
  · simpa only [mul_left_comm, mul_assoc, mul_comm] using Nat.mul_le_mul_left (lcmInterval n 5) hlo
  · simpa only [mul_left_comm, mul_assoc, mul_comm] using Nat.mul_le_mul_left (lcmInterval n 5) hhi

private theorem fiveBlockProduct_scaled_le {a b m n : ℕ}
    (h : ∀ i, 1 ≤ i → i ≤ 5 → a*(m+i) ≤ b*(n+i)) :
    a^5 * fiveBlockProduct m ≤ b^5 * fiveBlockProduct n := by
  have expand (c x : ℕ) : c^5 * fiveBlockProduct x =
      (c*(x+1))*(c*(x+2))*(c*(x+3))*(c*(x+4))*(c*(x+5)) := by unfold fiveBlockProduct; ring
  rw [expand, expand]
  repeat first | exact h _ (by decide) (by decide) | apply Nat.mul_le_mul

/-- A length-five collision has positive gap exceeding one seventeenth of
the first entry, and the later endpoint is less than five thirds of the earlier endpoint. -/
theorem five_collision_location {n m : ℕ} (hnm : n < m)
    (heq : lcmInterval m 5 = lcmInterval n 5) :
    n+1 < 17*(m-n) ∧ 3*(m+5) < 5*(n+5) := by
  obtain ⟨hlo, hhi⟩ := fiveBlockProduct_bounds_of_collision hnm heq
  have hpos : 0 < fiveBlockProduct n := by
    unfold fiveBlockProduct
    positivity
  constructor <;> by_contra! h
  · have hb := fiveBlockProduct_scaled_le (a := 17) (b := 18) (m := m) (n := n) (by intros; omega)
    omega
  · have hb := fiveBlockProduct_scaled_le (a := 5) (b := 3) (m := n) (n := m) (by intros; omega)
    omega

/-- Two distinct overlapping length-five blocks have the same LCM precisely at
these four ordered pairs of starts. -/
theorem five_overlap_collisions {n m : ℕ} (hlt : n < m) (hover : m < n+5) :
    lcmInterval m 5 = lcmInterval n 5 ↔
      (n,m) = (0,1) ∨ (n,m) = (4,5) ∨ (n,m) = (9,10) ∨ (n,m) = (14,15) := by
  constructor
  · intro heq
    have hgap := (five_collision_location hlt heq).1
    have checked : ∀ i : Fin 67, ∀ j : Fin 4, let a := i.val; let b := a+j.val+1
        lcmInterval b 5 = lcmInterval a 5 →
          (a,b) = (0,1) ∨ (a,b) = (4,5) ∨ (a,b) = (9,10) ∨ (a,b) = (14,15) := by decide
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact checked ⟨n, by omega⟩ ⟨d, by omega⟩ heq
  · rintro (h | h | h | h) <;> cases h <;> decide

end Erdos677
