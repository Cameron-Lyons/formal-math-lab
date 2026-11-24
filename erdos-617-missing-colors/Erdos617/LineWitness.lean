import Erdos617.LineObstruction

namespace Erdos617

open Finset SimpleGraph

/-- A missing-color theorem for every coloring with graph H in color k lifts to
colorings whose k-graph contains H, if H already meets every (r+1)-set. -/
theorem missing_of_spanning_subgraph {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 2 ≤ r) (c : Sym2 V → Fin r) (k : Fin r) (H : SimpleGraph V)
    (hsub : H ≤ colorGraph c k) (hα : H.indepNum ≤ r)
    (hsolve : ∀ d : Sym2 V → Fin r, colorGraph d k = H →
      ∃ (S : Finset V) (l : Fin r), S.card = r+1 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → d s(u,v) ≠ l) :
    ∃ (S : Finset V) (l : Fin r), l ≠ k ∧ S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ l := by
  classical
  obtain ⟨j,hj⟩ : (univ.erase k).Nonempty := card_pos.mp (by simp; omega)
  have hjk := (mem_erase.mp hj).1
  let d (e : Sym2 V) := if c e = k ∧ e ∉ H.edgeSet then j else c e
  have eq : colorGraph d k = H := by
    ext x y
    rw [colorGraph_adj]
    by_cases hh : H.Adj x y
    · have hc := ((colorGraph_adj ..).mp (hsub hh)).2
      simp [d,mem_edgeSet,hh,hc,hh.ne]
    · by_cases hc : c s(x,y) = k <;> simp [d,mem_edgeSet,hh,hc,hjk]
  obtain ⟨S,l,hcard,hmiss⟩ := hsolve d eq
  have hlk : l ≠ k := by
    rintro rfl
    have hind : H.IsIndepSet (S : Set V) := by
      intro u hu v hv huv hadj
      exact hmiss u hu v hv huv ((eq ▸ hadj : (colorGraph d l).Adj u v).2)
    have := hind.card_le_indepNum
    omega
  refine ⟨S,l,hlk,hcard,?_⟩
  intro u hu v hv huv hc
  apply hmiss u hu v hv huv
  simp [d,hc,hlk]

/-- A spanning line subgraph in color k suffices if it has independence number
at most r and average degree at most r. The missing color can be chosen distinct from k. -/
theorem missing_of_sparse_line_subgraph {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L]
    {r : ℕ} (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (k : Fin r) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hsub : H ≤ colorGraph c k) (hα : H.indepNum ≤ r) (he : 2*H.edgeFinset.card ≤ r*Fintype.card V)
    (hline : ∃ p : V → Sym2 L, LineRepresentation H univ p) :
    ∃ (S : Finset V) (l : Fin r), l ≠ k ∧ S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ l := by
  apply missing_of_spanning_subgraph (by omega) c k H hsub hα
  intro d eq
  have hedge : (colorGraph d k).edgeFinset = H.edgeFinset := by
    ext e
    rw [mem_edgeFinset,mem_edgeFinset,eq]
  exact missing_of_sparse_line_representation hr hn d k (hedge ▸ he) (eq ▸ hline)

end Erdos617
