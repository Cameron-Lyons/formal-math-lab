module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum

public section

namespace A176755

/-- The integer sequence in OEIS A176755, defined by its nonlinear recurrence. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | n + 2 => (∑ p : Fin (n + 2), a p * a (n + 1 - p)) - 2
termination_by n => n
decreasing_by all_goals have := Fin.isLt p; omega

@[simp] theorem a_zero : a 0 = 1 := by rw [a]

@[simp] theorem a_one : a 1 = 3 := by rw [a]

/-- The defining recurrence, with the ordinary inclusive convolution sum. -/
theorem a_recurrence (n : ℕ) (hn : 1 ≤ n) :
    a (n + 1) = (∑ p ∈ Finset.range (n + 1), a p * a (n - p)) - 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := a.eq_3 k
  rw [Fin.sum_univ_eq_sum_range (fun p => a p * a (k + 1 - p))] at h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

end A176755
