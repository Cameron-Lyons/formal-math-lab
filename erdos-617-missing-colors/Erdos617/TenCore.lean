import Erdos617.RankFiveRange

namespace Erdos617

open Finset SimpleGraph

/-- On 51 vertices, a rank-five minimal obstruction in ten colors costs
at least 281 edges of its distinguished color. -/
theorem MinimalObstruction.ten_five_edges {V : Type*} [DecidableEq V]
    {c : Sym2 V → Fin 10} {k : Fin 10} {S : Finset V}
    (h : MinimalObstruction c k 5 S) (hb : Balanced c) :
    281≤blockEdges (colorGraph c k) S := by
  classical
  let G := colorGraph c k
  have size : S.card=51 := h.card_eq
  have rk : rankOn G S=5 := h.rank_eq (by decide)
  obtain ⟨d,W,cost,ws,sz,rkW,eq,avg,charges⟩ := h.rank_shell hb (by decide) (by decide)
    (Subset.rfl : S⊆S) (card_pos.mp (by omega))
  change rankOn G W+1≤rankOn G S at rkW
  have lim {D : Finset V} (sub : D⊂S) (j : ℕ) (cap : rankOn G D≤j) : D.card≤j*10 := by
    obtain ⟨I,hi,ind,bound⟩ := h.proper_subset (by decide) D sub
    exact bound.trans (Nat.mul_le_mul_right 10 ((card_le_rankOn G hi ind).trans cap))
  have wc := lim ws 4 (by omega)
  change S.card*d≤2*blockEdges G S at avg
  change 281≤blockEdges G S
  by_contra! small
  rw [size] at avg sz
  have deq : d=10 := by omega
  have wn : W.card=40 := by omega
  have density := h.rank_four_at_four_rows (by decide) hb ws wn (by change rankOn G W≤4; omega)
  change 2*10*(10+1)≤blockEdges G W+8 at density
  have pairs := (charges 10 (by
    intro D sub cD
    change rankOn G D+2≤rankOn G S at cD
    have upper := lim (sub.trans_ssubset ws) 3 (by omega)
    omega)).2.1 deq
  change blockEdges G S=(d+1).choose 2+cost+blockEdges G W at eq
  rw [deq] at eq
  norm_num [Nat.choose] at eq
  omega

end Erdos617
