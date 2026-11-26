module

public import Erdos617.DeletionRank

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

/-- The foreign colors leave at most 112 edges of the obstruction color.
The order and minimum degree then force a vertex of degree exactly seven. -/
theorem MinimalObstruction.seven_edge_profile {V : Type*} [DecidableEq V]
    {c : Sym2 V → Fin 7} {k : Fin 7} {S : Finset V} (h : MinimalObstruction c k 4 S)
    (hb : Balanced c) :
    blockEdges (colorGraph c k) S≤112 ∧ ∃ x∈S,(S.filter ((colorGraph c k).Adj x)).card=7 := by
  classical
  let d := fun e : Sym2 S => c (Sym2.map Subtype.val e)
  have n : S.card=29 := h.card_eq
  have total := sum_color_edges d
  rw [←sum_erase_add _ _ (mem_univ k),Fintype.card_coe,n] at total
  have foreign := h.foreign_edge_sum hb (by decide)
  change (7-1)*(7*Nat.choose 4 2+2*4-1) ≤ ∑ j∈univ.erase k, (colorGraph d j).edgeFinset.card at foreign
  norm_num [Nat.choose] at total foreign
  have limit : blockEdges (colorGraph c k) S≤112 := by
    rw [color_blockEdges_eq]
    change (colorGraph d k).edgeFinset.card≤112
    omega
  refine ⟨limit,?_⟩
  by_contra! hnone
  have low := sum_le_sum (s:=S) (f:=fun _ => 8) (g:=fun x => (S.filter ((colorGraph c k).Adj x)).card)
    (fun x hx => by have := h.degree_ge x hx; have := hnone x hx; omega)
  rw [block_degree_sum,sum_const,nsmul_eq_mul,n] at low
  norm_num at low
  omega

end Erdos617
