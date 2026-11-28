module

public import Erdos617.TenCore
public import Erdos617.EvenEndpoint

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {c : Sym2 V → Fin 10} {k : Fin 10}

private theorem ten_no_smaller_rank (hb : Balanced c) (q : ℕ) (hq : q<5) (W : Finset V)
    (h : MinimalObstruction c k q W) : False := by
  have := h.five_le_of_nine_le hb (by decide) (by omega)
  omega

/-- The 281-edge bound extends to every set of rank five on at least 51 vertices.
Deleting a vertex above this order removes at least ten edges. -/
theorem ten_rank_five_support (hb : Balanced c) (A : Finset V) (rk : rankOn (colorGraph c k) A=5)
    (sz : 51≤A.card) : 10*A.card ≤ blockEdges (colorGraph c k) A+229 := by
  obtain ⟨W,_,h,shrink⟩ := extract_minimal_with_edge_slope (by decide : 0<5)
    (ten_no_smaller_rank hb) A rk.le sz
  have n : W.card=51 := h.card_eq
  have floor := h.ten_five_edges hb
  omega

/-- Ten colors in the original missing-color interface. -/
theorem ten_colors [Fintype V] (hn : Fintype.card V=10^2+1) (c : Sym2 V → Fin 10) :
    ∃ (S : Finset V) (k : Fin 10), S.card=10+1 ∧
      ∀ u∈S, ∀ v∈S, u≠v → c s(u,v)≠k := by
  by_contra no
  have hb := balanced_of_no_witness c no
  obtain ⟨k,sparse⟩ := exists_color_edge_budget (by decide) hn c
  obtain ⟨S,h,upper⟩ := even_endpoint_sparse_core (by decide : 2≤5) (by decide) hn c hb k sparse
    (ten_no_smaller_rank hb)
  have floor := h.ten_five_edges hb
  rw [h.card_eq] at upper
  norm_num [Nat.choose] at upper
  omega

end Erdos617
