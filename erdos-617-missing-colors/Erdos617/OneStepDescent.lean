import Erdos617.OnePairMerge
import Erdos617.RowDescent

namespace Erdos617

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- On a square of side r−1, two original colors pass the smaller balance
test. A merger succeeds exactly when at most two original colors can be
missed and the two-color group, if needed, hits every r-set. -/
theorem one_step_descent (hr : 5≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-1)^2+1 ∧
      let d := fun e : Sym2 U => c (e.map Subtype.val)
      let bad := univ.filter fun a => ¬ HitsPalette d (r-1) {a}
      i∉bad ∧ j∉bad ∧
        ((∃ f : Fin r → Fin (r-1), Balanced (f ∘ d)) ↔
          bad.card≤2 ∧ ∀ a b : Fin r, a≠b → a∈bad → b∈bad → HitsPalette d (r-1) {a,b}) := by
  classical
  obtain ⟨i,j,U,ij,ord,ri,rj⟩ := exists_square_of_at_most_two_rows (by decide : 1≤2) hr hn hb
  refine ⟨i,j,U,ij,ord,?_⟩
  let d := fun e : Sym2 U => c (e.map Subtype.val)
  have nonempty : ∃ S : Finset U,S.card=r := by
    have pred : r-1+1=r := by omega
    have bound : r≤(univ : Finset U).card := by
      rw [card_univ,Fintype.card_coe,ord]
      have := Nat.mul_le_mul_left (r-1) (show 1≤r-1 by omega)
      simpa [pow_two] using (show r≤(r-1)*(r-1)+1 by omega)
    obtain ⟨T,_,sz⟩ := exists_subset_card_eq bound
    exact ⟨T,sz⟩
  have hi : HitsPalette d (r-1) {i} := single_hit_of_rank c i ri
  have hj : HitsPalette d (r-1) {j} := single_hit_of_rank c j rj
  refine ⟨?_,?_,one_pair_merge_or_obstruction (by omega) d nonempty⟩
  · exact fun mem => (mem_filter.mp mem).2 hi
  · exact fun mem => (mem_filter.mp mem).2 hj

end Erdos617
