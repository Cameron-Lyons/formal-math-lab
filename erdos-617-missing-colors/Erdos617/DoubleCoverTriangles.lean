import Erdos617.OddBags

namespace Erdos617

open Finset SimpleGraph

variable {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- In a twofold cover by monochromatic cliques, each third clique removes
a rectangle of possible foreign edges between a given pair of cliques. -/
theorem double_cover_triangle_budget (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (S : Finset V) (B : ι → Finset V) (hsub : ∀ i, B i ⊆ S)
    (hcl : ∀ i, (colorGraph c k).IsClique (B i : Set V))
    (htwo : ∀ x ∈ S, (univ.filter fun i => x ∈ B i).card = 2) (i j : ι) (hij : i ≠ j) :
    (r-1)*((B i ∪ B j).card-r) +
        (∑ z ∈ (univ.erase i).erase j, (B i ∩ B z).card*(B j ∩ B z).card) ≤
      (B i \ B j).card*(B j \ B i).card := by
  classical
  have no_three {a b d : ι} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
      {x : V} (ha : x ∈ B a) (hb' : x ∈ B b) (hd : x ∈ B d) : False := by
    have sub : {a,b,d} ⊆ univ.filter (fun z => x ∈ B z) := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      exact mem_filter.mpr ⟨mem_univ _, hz.elim (· ▸ ha) (fun h => h.elim (· ▸ hb') (· ▸ hd))⟩
    have bound := card_le_card sub
    rw [htwo x (hsub a ha)] at bound
    simp [hab,had,hbd] at bound
  let T := (univ.erase i).erase j
  let R (z : ι) := (B i ∩ B z) ×ˢ (B j ∩ B z)
  let P := (B i \ B j) ×ˢ (B j \ B i)
  have distinct {z : ι} (hz : z ∈ T) : z ≠ i ∧ z ≠ j :=
    ⟨(mem_erase.mp (mem_erase.mp hz).2).1,(mem_erase.mp hz).1⟩
  have sub : T.biUnion R ⊆ P := by
    intro p hp
    obtain ⟨z,hz,hp⟩ := mem_biUnion.mp hp
    obtain ⟨hx,hy⟩ := mem_product.mp hp
    obtain ⟨hxi,hxz⟩ := mem_inter.mp hx
    obtain ⟨hyj,hyz⟩ := mem_inter.mp hy
    obtain ⟨hzi,hzj⟩ := distinct hz
    exact mem_product.mpr ⟨mem_sdiff.mpr ⟨hxi, fun hxj => no_three hij hzi.symm hzj.symm hxi hxj hxz⟩,
      mem_sdiff.mpr ⟨hyj, fun hyi => no_three hij hzi.symm hzj.symm hyi hyj hyz⟩⟩
  have disj : (↑T : Set ι).PairwiseDisjoint R := by
    intro z hz w hw hzw
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨hxi,hxz⟩ := mem_inter.mp (mem_product.mp hp).1
    have hxw := (mem_inter.mp (mem_product.mp hq).1).2
    exact no_three (distinct hz).1.symm (distinct hw).1.symm hzw hxi hxz hxw
  have total := foreign_pair_budget c hb k (B i ∪ B j) (P \ T.biUnion R) (by
    intro x hx y hy hxy hcol
    have h1 : ¬ (x ∈ B i ∧ y ∈ B i) := fun h => hcol (hcl i h.1 h.2 hxy).2
    have h2 : ¬ (x ∈ B j ∧ y ∈ B j) := fun h => hcol (hcl j h.1 h.2 hxy).2
    have avoid (u v : V) (huv : u ≠ v) (hcol' : c s(u,v) ≠ k) : (u,v) ∉ T.biUnion R := by
      intro hmem
      obtain ⟨z,_,hp⟩ := mem_biUnion.mp hmem
      exact hcol' (hcl z (mem_inter.mp (mem_product.mp hp).1).2
        (mem_inter.mp (mem_product.mp hp).2).2 huv).2
    have orient : (x,y) ∈ P ∨ (y,x) ∈ P := by
      simp only [P,mem_union,mem_product,mem_sdiff] at *
      grind
    exact orient.imp (fun hp => mem_sdiff.mpr ⟨hp,avoid x y hxy hcol⟩)
      (fun hp => mem_sdiff.mpr ⟨hp,avoid y x hxy.symm (by rwa [Sym2.eq_swap])⟩))
  have hc := card_sdiff_add_card_inter P (T.biUnion R)
  rw [inter_eq_right.mpr sub,card_biUnion disj] at hc
  simp only [P,R,card_product] at hc
  change (P \ T.biUnion R).card + (∑ z ∈ T,(B i ∩ B z).card*(B j ∩ B z).card) =
    (B i \ B j).card*(B j \ B i).card at hc
  change (r-1)*((B i ∪ B j).card-r)+(∑ z ∈ T,(B i ∩ B z).card*(B j ∩ B z).card) ≤ _
  by_cases lower : r ≤ (B i ∪ B j).card
  · have split := congrArg ((r-1)*·) (Nat.sub_add_cancel lower)
    rw [Nat.mul_add] at split
    omega
  · rw [Nat.sub_eq_zero_of_le (by omega : (B i ∪ B j).card ≤ r)]
    omega

end Erdos617
