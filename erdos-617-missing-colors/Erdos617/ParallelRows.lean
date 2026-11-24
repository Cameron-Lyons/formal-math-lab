import Erdos617.ParallelRowGreedy
import Erdos617.ParallelRowEdgeCount

namespace Erdos617

open Finset SimpleGraph

/-- The conjectured (r+1)-vertex witness exists whenever one color contains
r pairwise disjoint r-cliques. All edges between the rows may be arbitrary. -/
theorem missing_of_parallel_full_cliques {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (k : Fin r)
    (R : Fin r → Finset V) (full : ∀ i,(colorGraph c k).IsNClique r (R i))
    (dis : Pairwise fun i j => Disjoint (R i) (R j)) :
    ∃ (S : Finset V) (j : Fin r), S.card=r+1 ∧ ∀ u∈S,∀ v∈S,u≠v → c s(u,v)≠j := by
  classical
  by_contra absent
  have hb := balanced_of_no_witness c absent
  let Y := univ.biUnion R
  have sz : Y.card=r^2 := by
    simp only [Y,card_biUnion (fun _ _ _ _ ne => dis ne),fun i => (full i).card_eq,
      sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,pow_two]
  have one : Yᶜ.card=1 := by rw [card_compl,hn,sz]; omega
  obtain ⟨x,last⟩ := card_eq_one.mp one
  have outside (i : Fin r) : x∉R i := by
    have m : x∈Yᶜ := last ▸ mem_singleton_self _
    exact fun h => mem_compl.mp m (mem_biUnion.mpr ⟨i,mem_univ _,h⟩)
  obtain ⟨spokes,cross⟩ := parallel_row_forcing c k hr hb R full dis x outside
  exact parallel_row_budget_impossible hr hn c hb k
    (parallel_row_edge_floor (colorGraph c k) R full dis x outside (by
      change {x}∪Y=univ
      rw [←last]
      ext u
      by_cases h : u∈Y <;> simp [h]) spokes cross)

end Erdos617
