module

public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace ThreeColumnMatrices
open Finset

/-- Column supports of size at most two that contain every row in `t`. -/
def columnSupports {n : ℕ} (t : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  univ.filter (fun s => s.card ≤ 2 ∧ t ⊆ s)

@[simp] theorem mem_columnSupports {n : ℕ} {t s : Finset (Fin n)} :
    s ∈ columnSupports t ↔ s.card ≤ 2 ∧ t ⊆ s := by simp [columnSupports]

/-- The number of choices left in one column when the rows in `t` are prescribed. -/
theorem card_columnSupports {n : ℕ} (t : Finset (Fin n)) :
    (columnSupports t).card = match t.card with
      | 0 => 1 + n + n.choose 2
      | 1 => n
      | 2 => 1
      | _ + 3 => 0 := by
  -- Choose the remaining `k - t.card` ones outside the prescribed rows.
  have extensions (k : ℕ) : ((univ.powersetCard k).filter (t ⊆ ·)).card =
      if t.card ≤ k then (n - t.card).choose (k - t.card) else 0 := by
    split <;> rename_i h
    · simpa using card_filter_powersetCard_subset t univ k (subset_univ _) h
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro s hs hts
      exact h ((card_le_card hts).trans_eq (mem_powersetCard_univ.mp hs))
  -- Group the column supports by size and sum over sizes zero, one and two.
  have bySize : (columnSupports t).card =
      ∑ k ∈ range 3, ((univ.powersetCard k).filter (t ⊆ ·)).card := by
    have fibers := sum_card_fiberwise_eq_card_filter (univ.filter (t ⊆ ·)) (range 3) card
    simpa [filter_comm (p := (t ⊆ ·)), filter_filter, Nat.lt_succ_iff, columnSupports]
      using fibers.symm
  rw [bySize]
  simp only [sum_range_succ, sum_range_zero, zero_add, extensions]
  have ht : t.card ≤ n := by simpa using t.card_le_univ
  match h : t.card with
  | 0 => simp
  | 1 => simp; omega
  | 2 => simp
  | _ + 3 => simp

end ThreeColumnMatrices
