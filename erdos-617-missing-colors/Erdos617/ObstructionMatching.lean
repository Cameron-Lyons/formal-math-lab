import Erdos617.MatchingShell
import Erdos617.MinimumDegreeRange

namespace Erdos617

open Finset SimpleGraph

private theorem matching_cost_lower {r b z : ℕ} (wide : 2*b+3≤r)
    (bounds : ∀ m≤b+1, m*(r+1-b)≤z+(2*m).choose 2) :
    r*(b+1)≤16*z := by
  let m := b/4+1
  have mb : m≤b+1 := by dsimp [m]; omega
  have mm : b+1≤4*m := by dsimp [m]; omega
  have mq : 4*m≤b+4 := by dsimp [m]; omega
  have low := bounds m mb
  have c := twice_choose_two (2*m)
  have ch : (2*m).choose 2+m=2*m*m := by nlinarith only [c]
  have nb : r+1-b+b=r+1 := by omega
  have le : r+8*m≤4*(r+1-b)+4 := by omega
  nlinarith only [low,ch,Nat.mul_le_mul_right m le,Nat.mul_le_mul_left r mm]

/-- In every minimal obstruction in the half-range, deleting a minimum-degree
vertex and its neighbors leaves a set W of smaller rank. Write the number
deleted as r+b. Every matching size from 0 through b+1 gives a lower bound
on the edges paid in excess of choose(r+b,2) during this deletion. -/
theorem MinimalObstruction.matching_reduction {V : Type*} [DecidableEq V] {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (hr : 7≤r) (ht : 4≤t) (half : t≤(r+1)/2) (hb : Balanced c) :
    let G := colorGraph c k
    ∃ (b z : ℕ) (W : Finset V), 1≤b ∧ b+3≤t ∧ W⊂S ∧ W.card+(r+b)=S.card ∧
      rankOn G W<t ∧ blockEdges G S=(r+b).choose 2+z+blockEdges G W ∧
      (∀ m≤b+1, m*(r+1-b)≤z+(2*m).choose 2) ∧ r*(b+1)≤16*z := by
  classical
  intro G
  have pos : S.Nonempty := card_pos.mp (by rw [h.card_eq]; omega)
  have smaller : t<r := by omega
  obtain ⟨d,W,z,sub,num,rkw,ledger,avg,price⟩ := h.rank_matching_shell hb smaller
    (Subset.rfl : S⊆S) pos
  change blockEdges G S=(d+1).choose 2+z+blockEdges G W at ledger
  change rankOn G W+1≤rankOn G S at rkw
  have rk : rankOn G S=t := h.rank_eq (by omega)
  have order {D : Finset V} (hs : D⊂S) {a : ℕ} (rank : rankOn G D≤a) : D.card≤a*r := by
    obtain ⟨I,inc,ind,cap⟩ := h.proper_subset (by omega) D hs
    exact cap.trans (Nat.mul_le_mul_right r ((card_le_rankOn G inc ind).trans rank))
  have ordW := order sub (show rankOn G W≤t-1 by omega)
  have size := h.card_eq
  have tp : t-1+1=t := by omega
  have np := congrArg (·*r) tp
  simp only [Nat.add_mul,Nat.one_mul] at np
  let b := d+1-r
  have db : d+1=r+b := by dsimp [b]; omega
  have minimum := h.minimum_degree_range hb ht hr avg
  have wide : 2*b+3≤r := by omega
  have cost (m : ℕ) (hm : m≤b+1) : m*(r+1-b)≤z+(2*m).choose 2 := by
    apply price b _ db wide _ m hm
    intro D hD dr
    change rankOn G D+2≤rankOn G S at dr
    have lim := order (hD.trans_ssubset sub) (show rankOn G D≤t-2 by omega)
    have nr := congrArg (·*r) (show t-2+2=t by omega)
    simp only [Nat.add_mul] at nr
    omega
  refine ⟨b,z,W,by omega,by omega,sub,by omega,by omega,?_,cost,matching_cost_lower wide cost⟩
  rwa [db] at ledger

end Erdos617
