import Erdos617.LowCostSet

namespace Erdos617

open Finset SimpleGraph

/-- Applying the foreign edge floor to every other color bounds the minimum
degree in the obstruction color to within t−4 of r. -/
theorem MinimalObstruction.minimum_degree_range {V : Type*} [DecidableEq V] {r t d : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (hb : Balanced c) (ht : 4≤t) (hr : 7≤r)
    (avg : S.card*d≤2*blockEdges (colorGraph c k) S) : d+4≤r+t := by
  classical
  let cp := fun e : Sym2 S => c (Sym2.map Subtype.val e)
  let e := (colorGraph cp k).edgeFinset.card
  let F := ∑ j∈univ.erase k,(colorGraph cp j).edgeFinset.card
  have total := sum_color_edges cp
  rw [←sum_erase_add _ _ (mem_univ k),Fintype.card_coe,h.card_eq] at total
  change F+e=(t*r+1).choose 2 at total
  have other := h.foreign_edge_sum hb (by omega)
  change (r-1)*(r*t.choose 2+2*t-1)≤F at other
  rw [color_blockEdges_eq,h.card_eq] at avg
  change (t*r+1)*d≤2*e at avg
  by_contra! low
  have dn := Nat.mul_le_mul_left (t*r+1) (show r+t ≤ d+3 by omega)
  have pred : r-1+1=r := by omega
  have term : r*t.choose 2+2*t-1+1=r*t.choose 2+2*t := by omega
  have ch := congrArg (fun z => r*(r-1)*z) (twice_choose_two t)
  have card := twice_choose_two (t*r+1)
  have gap : r+3*t+2<t*r+1 := by
    obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hr
    obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le ht
    nlinarith only [Nat.zero_le (u*v),Nat.zero_le u,Nat.zero_le v]
  have hr' : (r-1)*r*t^2+r*t^2=r*r*t^2 := by nlinarith only [congrArg (·*(r*t^2)) pred]
  have hr'' : (r-1)*r*t+r*t=r*r*t := by nlinarith only [congrArg (·*(r*t)) pred]
  nlinarith only [avg,dn,total,other,ch,card,gap,pred,hr',hr'',congrArg (fun z => (r-1)*z) term,
    congrArg (·*(2*t)) pred]

end Erdos617
