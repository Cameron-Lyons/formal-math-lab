import Erdos617.CliqueRows
import Erdos617.EightProfile
import Erdos617.EightRows
import Erdos617.SmallRange

namespace Erdos617

open Finset SimpleGraph

/-- A rank-four obstruction cannot occur in any balanced eight-coloring. -/
theorem MinimalObstruction.not_eight_four {V : Type*} [DecidableEq V] {c : Sym2 V → Fin 8}
    {k : Fin 8} {S : Finset V} (h : MinimalObstruction c k 4 S) (hb : Balanced c) : False := by
  classical
  let G := colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k
  obtain ⟨n,deg,cost,cap,_⟩ := h.eight_energy_profile hb
  have com := h.eight_common_neighbors hb
  obtain ⟨Q,_,row,_,hole,low⟩ := eight_clique_rows G n deg com cap cost
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<(Q.biUnion id)ᶜ.card by omega)
  have out : x∉Q.biUnion id := mem_compl.mp hx
  obtain ⟨C,hxC,cl⟩ := exists_pointClique G x
  rw [low x out] at cl
  exact no_six_clique_outside_rows G deg cap com Q row hole.le out cl hxC

/-- The eight-color case of the Erdős–Gyárfás conjecture. -/
theorem eight_colors {V : Type*} [Fintype V] [DecidableEq V] (hn : Fintype.card V=8^2+1)
    (c : Sym2 V → Fin 8) : ∃ (S : Finset V) (k : Fin 8), S.card=8+1 ∧
      ∀ u∈S, ∀ v∈S, u≠v → c s(u,v)≠k := by
  by_contra bad
  have hb := balanced_of_no_witness c bad
  obtain ⟨k,t,S,_,upper,h⟩ := exists_minimalObstruction_ceil_half (by decide) hn c hb
  have lt : t<8 := by omega
  obtain ⟨_,_,_,_,_,_,half,_,two,_⟩ := h.exists_nested_product_obstruction (by decide) hb lt
  obtain rfl : t=4 := by omega
  exact h.not_eight_four hb

end Erdos617
