import Erdos617.LocalCliqueEnergy

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With maximum degree nine and at most two common neighbors for every
nonedge, a six-clique through an outside vertex cannot meet a seven-clique. -/
theorem no_six_clique_outside_rows (G : SimpleGraph V) [DecidableRel G.Adj]
    (deg : ∀ x, G.degree x≤9) (cap : ∀ x, pointClique G x≤7)
    (common : ∀ x y, x≠y → ¬G.Adj x y → (G.neighborFinset x ∩ G.neighborFinset y).card≤2)
    (Q : Finset (Finset V)) (row : ∀ A∈Q, G.IsNClique 7 A)
    (hole : (Q.biUnion id)ᶜ.card≤5) {x : V} (out : x∉Q.biUnion id)
    {C : Finset V} (six : G.IsNClique 6 C) (hx : x∈C) : False := by
  classical
  obtain ⟨y,hy,hyU⟩ : ∃ y∈C, y∈Q.biUnion id := by
    by_contra! none
    have sub : C ⊆ (Q.biUnion id)ᶜ := fun y hy => mem_compl.mpr (none y hy)
    have h := card_le_card sub
    rw [six.card_eq] at h
    omega
  obtain ⟨A,hA,hyA⟩ := mem_biUnion.mp hyU
  change y∈A at hyA
  have seven := row A hA
  have xout : x∉A := fun h => out (mem_biUnion.mpr ⟨A,hA,h⟩)
  obtain ⟨z,hz,non⟩ : ∃ z∈A, ¬G.Adj x z := by
    by_contra! near
    have big : G.IsClique (↑(insert x A) : Set V) := by
      rw [coe_insert]
      exact seven.isClique.insert (fun z hz _ => near z hz)
    have up := (card_le_pointClique G _ big x (mem_insert_self ..)).trans (cap x)
    rw [card_insert_of_notMem xout,seven.card_eq] at up
    omega
  have xz : x≠z := fun eq => xout (eq ▸ hz)
  have znot : z∉C := fun h => non (six.isClique hx h xz)
  have small : (A∩C).card≤2 := by
    refine (card_le_card (t:=G.neighborFinset x ∩ G.neighborFinset z) ?_).trans (common x z xz non)
    intro w hw
    obtain ⟨wa,wc⟩ := mem_inter.mp hw
    exact mem_inter.mpr ⟨(G.mem_neighborFinset x w).mpr (six.isClique hx wc (fun eq => xout (eq ▸ wa))),
      (G.mem_neighborFinset z w).mpr (seven.isClique hz wa (fun eq => znot (eq ▸ wc)))⟩
  have neighbors : (A∪C).erase y ⊆ G.neighborFinset y := by
    intro w hw
    obtain ⟨different,mem⟩ := mem_erase.mp hw
    rcases mem_union.mp mem with ha|hc
    · exact (G.mem_neighborFinset y w).mpr (seven.isClique hyA ha different.symm)
    · exact (G.mem_neighborFinset y w).mpr (six.isClique hy hc different.symm)
  have bound := (card_le_card neighbors).trans_eq (G.card_neighborFinset_eq_degree y)
  have lower := card_erase_add_one (mem_union_left C hyA)
  have count := card_union_add_card_inter A C
  rw [seven.card_eq,six.card_eq] at count
  have := deg y
  omega

end Erdos617
