import Erdos617.ClosedNeighborhoodSlack
import Erdos617.OddPrivateRows

namespace Erdos617

open Finset

/-- The nine-color case follows from the sparse color at the odd endpoint.
Deleting a degree-nine closed neighborhood leaves a saturated rank-four set. -/
theorem nine_colors {V : Type*} [Fintype V] [DecidableEq V] (hn : Fintype.card V=9^2+1)
    (c : Sym2 V → Fin 9) : ∃ (S : Finset V) (k : Fin 9), S.card=9+1 ∧
      ∀ u∈S, ∀ v∈S, u≠v → c s(u,v)≠k := by
  by_contra bad
  have hb := balanced_of_no_witness c bad
  have small (k : Fin 9) (a : ℕ) (ha : a≤4) (W : Finset V) (h : MinimalObstruction c k a W) : False := by
    have := h.five_le_of_nine_le hb (by decide) (by omega)
    omega
  obtain ⟨k,_,_,hk,_⟩ := odd_endpoint_two_sparse (s:=4) (by decide) (by decide) hn c hb small
  obtain ⟨S,P,h,sz,cover,dis,cl⟩ :=
    odd_endpoint_of_sparse_color (s:=4) (by decide) (by decide) hn c hb k hk (small k)
  have budget := odd_core_excess (s:=4) (by decide) (by decide) hk h P sz cover dis cl
  let G := colorGraph c k
  have sum : (∑ x∈S, ((S.filter (G.Adj x)).card-9))+S.card*9=2*blockEdges G S := by
    rw [←block_degree_sum,show S.card*9=∑ _∈S,9 by simp,←sum_add_distrib]
    exact sum_congr rfl (fun x hx => Nat.sub_add_cancel (h.degree_ge x hx))
  change (∑ x∈S, ((S.filter (G.Adj x)).card-9)) ≤ 4*9 at budget
  rw [h.card_eq] at sum
  exact h.not_nine_five_of_edges hb (by change blockEdges G S≤225; omega)

end Erdos617
