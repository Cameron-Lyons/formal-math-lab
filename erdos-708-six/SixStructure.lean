import PrimeParts
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Permutation
import Mathlib.Tactic

namespace IntervalSix
open Erdos708Slots

/-- In any window of length n, its entire product is divisible by n!. -/
theorem whole_window (L n : ℕ) (C : Finset ℕ) (hC : C ⊆ Finset.Icc 1 n) :
    Cover L n n (∏ c ∈ C, c) := by
  refine ⟨Finset.Ico L (L+n), Finset.Subset.rfl, by simp, ?_⟩
  have h₁ : (∏ c ∈ C, c) ∣ n.factorial := by
    rw [← Finset.prod_Ico_id_eq_factorial, Finset.Ico_add_one_right_eq_Icc]
    exact Finset.prod_dvd_prod_of_subset _ _ id hC
  refine h₁.trans ?_
  simpa [Finset.prod_Ico_eq_prod_range, Nat.ascFactorial_eq_prod_range] using
    L.factorial_dvd_ascFactorial n

/-- Every subset of at most three cofactors has an ordering that passes the gcd check. -/
private theorem cofactor_table : ∀ n : Fin 8, ∀ C ∈ (Finset.Icc 1 n.val).powerset,
    C.card ≤ 3 → ∃ ds ∈ ((List.range 8).filter (· ∈ C)).permutations',
      ds.length = C.card ∧ ds.prod = (∏ c ∈ C, c) ∧ slotOK n 0 1 ds := by
  set_option maxRecDepth 20000 in decide +kernel

theorem cofactor_cover (K n : ℕ) (C : Finset ℕ) (h7 : n ≤ 7)
    (hC : C ⊆ Finset.Icc 1 n) (hk : C.card ≤ 3) : Cover K n C.card (∏ c ∈ C, c) := by
  obtain ⟨ds, _, hlen, hprod, ok⟩ :=
    cofactor_table ⟨n, by omega⟩ C (Finset.mem_powerset.mpr hC) hk
  have emp : Cover K n 0 1 := ⟨∅, by simp, by simp, by simp⟩
  simpa [hlen, hprod] using slotOK_sound ds emp ok

end IntervalSix
