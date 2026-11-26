module

public import Erdos617.DeletionRank

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {c : Sym2 V → Fin 7} {k : Fin 7} {S : Finset V}

/-- Twenty-one vertices of rank at most three in a rank-four obstruction
induce at least 76 edges of the distinguished color. -/
theorem MinimalObstruction.seven_residual_edges (h : MinimalObstruction c k 4 S) (hb : Balanced c)
    {W : Finset V} (ws : W ⊆ S) (nw : W.card=21) (cap : rankOn (colorGraph c k) W≤3) :
    76≤blockEdges (colorGraph c k) W := by
  classical
  let G := colorGraph c k
  have ns : S.card=29 := h.card_eq
  have pw : W ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨ws,fun he => by rw [he,ns] at nw; contradiction⟩
  have bound {A : Finset V} (sub : A⊆W) : A.card≤rankOn G A*7 := by
    obtain ⟨I,hi,ind,sz⟩ := h.proper_subset (by decide) A (sub.trans_ssubset pw)
    exact sz.trans (Nat.mul_le_mul_right 7 (card_le_rankOn G hi ind))
  have low := bound (Subset.rfl : W⊆W)
  change rankOn G W ≤ 3 at cap
  have rw' : rankOn G W=3 := by omega
  have ins : RankInseparable G W := by
    refine ⟨card_pos.mp (by omega),?_⟩
    intro A B ha hB hd hu
    have subA : A⊆W := hu ▸ subset_union_left
    have subB : B⊆W := hu ▸ subset_union_right
    by_contra! small
    have eq := congrArg Finset.card hu
    rw [card_union_of_disjoint hd,nw] at eq
    have a := bound subA
    have b := bound subB
    have highA := h.three_le_tight_rank hb (by decide) (by decide) (subA.trans ws) ha
      (by change A.card=rankOn G A*7; omega)
    have highB := h.three_le_tight_rank hb (by decide) (by decide) (subB.trans ws) hB
      (by change B.card=rankOn G B*7; omega)
    change 3≤rankOn G A at highA
    change 3≤rankOn G B at highB
    omega
  have density := rank_density G W ins 7
  have strict : 7*W.card < blockEdges G W+(Nat.choose 7 2+1)*rankOn G W+(7-1) := by
    refine lt_of_le_of_ne density fun equality => ?_
    obtain ⟨C,hC,cl⟩ := exists_clique_of_saturated_rank_density_eq G W ins 7 (by decide) rw'.ge
      (by rw [nw,rw']) equality
    exact h.no_clique hb (by decide) C (hC.trans ws) cl
  norm_num [nw,rw',Nat.choose] at strict
  change 76≤blockEdges G W
  omega

/-- If two nonadjacent vertices outside W have, in total, at most seven
neighbors in W, the residue contradicts the rank-two order bound. -/
theorem MinimalObstruction.seven_no_light_pair (h : MinimalObstruction c k 4 S) (hb : Balanced c)
    {W : Finset V} (ws : W⊆S) (nw : W.card=21) {y z : V}
    (ys : y∈S) (zs : z∈S) (yw : y∉W) (zw : z∉W) (yz : y≠z) (no : ¬(colorGraph c k).Adj y z)
    (light : (W.filter ((colorGraph c k).Adj y)).card+(W.filter ((colorGraph c k).Adj z)).card≤7) :
    False := by
  classical
  let G := colorGraph c k
  let D := W.filter (G.Adj y) ∪ W.filter (G.Adj z)
  let A := W \ D
  have sub : D ⊆ W := union_subset (filter_subset ..) (filter_subset ..)
  have size := card_sdiff_add_card_eq_card sub
  have dcap := (card_union_le (W.filter (G.Adj y)) (W.filter (G.Adj z))).trans light
  change D.card≤7 at dcap
  change A.card+D.card=W.card at size
  obtain ⟨I,hi,ind,eq⟩ := exists_max_indep G A
  have iW : I⊆W := hi.trans sdiff_subset
  have yi : y∉I := fun hy => yw (iW hy)
  have zi : z∉insert y I := by simp [Ne.symm yz,show z∉I from fun hz => zw (iW hz)]
  have ay := independent_insert_of_nonadjacent G ind y (by
    intro v hv e
    exact (mem_sdiff.mp (hi hv)).2 (mem_union_left _ (mem_filter.mpr ⟨iW hv,e⟩)))
  have az := independent_insert_of_nonadjacent G ay z (by
    intro v hv e
    rcases mem_insert.mp hv with eq | hv
    · subst v; exact no e.symm
    · exact (mem_sdiff.mp (hi hv)).2 (mem_union_right _ (mem_filter.mpr ⟨iW hv,e⟩)))
  have upper := card_le_rankOn G (insert_subset zs (insert_subset ys (iW.trans ws))) az
  rw [card_insert_of_notMem zi,card_insert_of_notMem yi,eq] at upper
  have rk : rankOn G S=4 := h.rank_eq (by decide)
  have small := h.rank_two_card_lt hb (by decide) (by decide) (sdiff_subset.trans ws : A⊆S)
    (by change rankOn G A≤2; omega)
  change A.card<14 at small
  omega

end Erdos617
