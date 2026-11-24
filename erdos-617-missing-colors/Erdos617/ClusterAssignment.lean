import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

namespace Erdos617

open Finset

/-- Assign every vertex to two distinct parts. If their respective costs are
at most L and q, the total cost of the assignments is at most |X|*(L+q). -/
theorem double_cluster_assignment {V ι : Type*} [Fintype ι] (X : Finset V)
    (cost : V → ι → ℕ) (L q : ℕ)
    (h : ∀ x ∈ X, ∃ i j, i ≠ j ∧ cost x i ≤ L ∧ cost x j ≤ q) :
    ∃ Y : ι → Finset V, (∀ i, Y i ⊆ X) ∧ (∑ i, (Y i).card) = 2*X.card ∧
      (∑ i, ∑ x ∈ Y i, cost x i) ≤ X.card*(L+q) := by
  classical
  have pick (x : V) : ∃ J : Finset ι, x ∈ X →
      J.card = 2 ∧ (∑ i ∈ J, cost x i) ≤ L+q := by
    by_cases hx : x ∈ X
    · obtain ⟨i,j,hij,hi,hj⟩ := h x hx
      refine ⟨{i,j},fun _ => ?_⟩
      simpa [hij] using Nat.add_le_add hi hj
    · exact ⟨∅,fun h => (hx h).elim⟩
  choose J cert using pick
  let Y (i : ι) := X.filter fun x => i ∈ J x
  have transpose (f : V → ι → ℕ) :
      (∑ i, ∑ x ∈ Y i, f x i) = ∑ x ∈ X, ∑ i ∈ J x, f x i := by
    simp_rw [Y, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    rw [← sum_filter]
    simp
  refine ⟨Y, fun _ => filter_subset .., ?_, ?_⟩
  · have counted := transpose (fun _ _ => 1)
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_one] at counted
    rw [counted,sum_congr rfl (fun x hx => (cert x hx).1)]
    simp [Nat.mul_comm]
  · rw [transpose]
    simpa using sum_le_sum (fun x hx => (cert x hx).2)

end Erdos617
