module

public import Erdos617.GlobalCliqueEnergy
public import Erdos617.PaletteNormalization

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

omit [DecidableEq V] in
theorem rankOn_univ_eq_indepNum (G : SimpleGraph V) : rankOn G univ=G.indepNum := by
  obtain ⟨I,_,hi,hr⟩ := exists_max_indep G univ
  obtain ⟨J,hj⟩ := G.exists_isNIndepSet_indepNum
  refine le_antisymm (hr ▸ hi.card_le_indepNum) ?_
  exact hj.card_eq ▸ card_le_rankOn G (subset_univ J) hj.isIndepSet

theorem balanced_clique_cap (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (hr : 2≤r) {B : Finset V} (hB : (colorGraph c k).IsClique (B : Set V)) : B.card ≤ r := by
  obtain ⟨j,hj⟩ : (univ.erase k).Nonempty := card_pos.mp (by simp; omega)
  have hji := (mem_erase.mp hj).1
  have ind : (colorGraph c j).IsIndepSet (B : Set V) := by
    intro x hx y hy ne e
    exact hji (e.2.symm.trans (hB hx hy ne).2)
  exact ind.card_le_indepNum.trans (balanced_indepNum_le c hb j)

private theorem clique_within_one_part (G : SimpleGraph V) (P : Finset (Finset V))
    (hu : P.biUnion id=univ) (hd : (↑P : Set (Finset V)).PairwiseDisjoint id) {C : Finset V}
    (hc : (withinParts G P).IsClique (C : Set V)) {x : V} (hx : x∈C) :
    ∃ A∈P, C⊆A := by
  have hy : x∈P.biUnion id := hu ▸ mem_univ x
  obtain ⟨A,ha,hxA⟩ := mem_biUnion.mp hy
  refine ⟨A,ha,fun z hz => ?_⟩
  by_cases eq : x=z
  · exact eq ▸ hxA
  obtain ⟨B,hB,hxB,hzB⟩ := (hc hx hz eq).2
  by_contra h
  have ne : A≠B := fun eq => h (eq ▸ hzB)
  exact disjoint_left.mp (hd ha hB ne) hxA hxB

/-- A family of full monochromatic cliques that can all be removed at once,
decreasing the upper bound on independence by one for each member. -/
structure FullCliqueRows (c : Sym2 V → Fin r) (k : Fin r) (Q : Finset (Finset V)) : Prop where
  disjoint : (↑Q : Set (Finset V)).PairwiseDisjoint id
  full : ∀ B∈Q,(colorGraph c k).IsNClique r B
  residual : rankOn (colorGraph c k) (univ \ Q.biUnion id)+Q.card ≤ r

/-- Every full independent set meets each row exactly once, including every
full monochromatic clique in another color of the original coloring. -/
theorem FullCliqueRows.transversal {c : Sym2 V → Fin r} {k : Fin r} {Q : Finset (Finset V)}
    (h : FullCliqueRows c k Q) {D : Finset V} (hD : (colorGraph c k).IsNIndepSet r D) :
    (D ∩ (univ \ Q.biUnion id)).card=r-Q.card ∧ ∀ B∈Q,(D∩B).card=1 := by
  let R := univ \ Q.biUnion id
  have sub : Q.biUnion id=univ \ R := by ext x; simp [R]
  have low := card_le_rankOn (colorGraph c k) (inter_subset_right : D∩R⊆R)
    (hD.isIndepSet.mono inter_subset_left)
  have cap : rankOn (colorGraph c k) R+Q.card≤r := h.residual
  have one (B : Finset V) (hb : B∈Q) : (D∩B).card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra ne
    exact hD.isIndepSet (mem_inter.mp hx).1 (mem_inter.mp hy).1 ne
      ((h.full B hb).isClique (mem_inter.mp hx).2 (mem_inter.mp hy).2 ne)
  have split := card_inter_complement_sum R D Q sub h.disjoint
  rw [hD.card_eq] at split
  have sum := sum_le_sum one
  simp only [sum_const,nsmul_eq_mul,Nat.mul_one,Nat.cast_id] at sum
  refine ⟨?_,(sum_eq_sum_iff_of_le one).mp ?_⟩
  · change (D∩R).card=_
    omega
  · simp only [sum_const,nsmul_eq_mul,Nat.mul_one,Nat.cast_id]
    omega

private theorem full_packing_on_partition (hr : 3≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (P : Finset (Finset V))
    (hu : P.biUnion id=univ) (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hi : ∀ A∈P, RankInseparable (colorGraph c k) A)
    (hα : (∑ A∈P,rankOn (colorGraph c k) A)=rankOn (colorGraph c k) univ) (parts : 2≤P.card) :
    ∃ Q : Finset (Finset V), FullCliqueRows c k Q ∧
      r*Fintype.card V+2*r+1+(∑ x∈univ \ Q.biUnion id,(r-1-pointClique (colorGraph c k) x)) ≤
        2*(colorGraph c k).edgeFinset.card+r*Q.card := by
  classical
  let G := colorGraph c k
  change ∑ A∈P, rankOn G A=rankOn G univ at hα
  change ∀ A∈P, RankInseparable G A at hi
  have cap : rankOn G univ ≤ r := (rankOn_univ_eq_indepNum G).le.trans (balanced_indepNum_le c hb k)
  have small (A : Finset V) (ha : A∈P) : rankOn G A < r := by
    have lb := sum_le_sum (s:=P.erase A) (f:=fun _ => 1)
      (fun B hB => (hi _ (mem_of_mem_erase hB)).rank_pos)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_erase_of_mem ha] at lb
    have eq := sum_erase_add P (rankOn G) ha
    rw [hα] at eq
    omega
  let Q := P.filter fun B => G.IsNClique r B
  let X := Q.biUnion id
  have disQ : (↑Q : Set (Finset V)).PairwiseDisjoint id :=
    fun _ ha _ hb ne => hd (mem_filter.mp ha).1 (mem_filter.mp hb).1 ne
  have clQ (A : Finset V) (ha : A∈Q) : G.IsNClique r A := (mem_filter.mp ha).2
  have xcount : X.card=Q.card*r := by
    have h := card_biUnion disQ
    change X.card=∑ A∈Q,A.card at h
    simpa only [sum_congr rfl (fun A ha => (clQ A ha).card_eq),sum_const,nsmul_eq_mul,Nat.cast_id] using h
  let H := withinParts G P
  have hsub : H ≤ G := fun _ _ h => h.1
  have hRank : H.indepNum ≤ r := by
    rw [←rankOn_univ_eq_indepNum]
    have h := rankOn_withinParts G P hd univ hu.ge
    simpa only [univ_inter,hα] using h.le.trans (by simpa only [univ_inter,hα] using cap)
  have outside {x : V} (hx : x∉X) : pointClique H x < r := by
    obtain ⟨C,hxC,hC⟩ := exists_pointClique H x
    have clique : G.IsClique (C : Set V) := fun _ hu _ hv ne => hsub (hC.isClique hu hv ne)
    have ub := balanced_clique_cap c hb k (by omega) clique
    by_contra! big
    have size : C.card=r := by have := hC.card_eq; omega
    obtain ⟨A,ha,sub⟩ := clique_within_one_part G P hu hd hC.isClique hxC
    have one : rankOn G A=1 := by
      have pos := (hi A ha).rank_pos
      by_contra! ne
      exact (hi A ha).no_full_clique hb (by change 1<rankOn G A; omega) (small A ha) sub ⟨clique,size⟩
    have all := rank_one_clique G one
    have acap := balanced_clique_cap c hb k (by omega) all
    have eq := eq_of_subset_of_card_le sub (acap.trans_eq size.symm)
    have haQ : A∈Q := mem_filter.mpr ⟨ha,all,eq ▸ size⟩
    exact hx (mem_biUnion.mpr ⟨A,haQ,sub hxC⟩)
  have full (x : V) : pointClique H x ≤ r := by
    obtain ⟨C,_,hC⟩ := exists_pointClique H x
    rw [←hC.card_eq]
    exact balanced_clique_cap c hb k (by omega) (fun _ hu _ hv ne => hsub (hC.isClique hu hv ne))
  let δ (x : V) := r-1-pointClique G x
  have per (x : V) (_ : x ∈ univ) :
      pointClique H x + (if x∈X then 0 else δ x) ≤ (r-1)+(if x∈X then 1 else 0) := by
    by_cases hx : x∈X
    · simp [hx]
      have := full x
      omega
    · have a := outside hx
      obtain ⟨C,hxC,hC⟩ := exists_pointClique H x
      have mono := card_le_pointClique G C (fun _ hu _ hv ne => hsub (hC.isClique hu hv ne)) x hxC
      rw [hC.card_eq] at mono
      simp only [hx,ite_false,Nat.add_zero,δ]
      omega
  have ub := sum_le_sum per
  have dsum : (∑ x, if x∈X then 0 else δ x) = ∑ x∈univ \ X,δ x := by
    rw [sum_ite]
    simp [show (univ.filter fun x => x∉X)=univ \ X by ext x; simp]
  have filt : (univ.filter fun x => x∈X)=X := by ext x; simp
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,sum_boole,dsum,filt] at ub
  have all := clique_energy_floor H hRank (by simpa only [pow_two] using hn : Fintype.card V=r*r+1)
  rw [H.sum_degrees_eq_twice_card_edges] at all
  have ecap := Nat.mul_le_mul_left 2 (card_le_card (edgeFinset_mono hsub))
  have arithmetic : r*Fintype.card V+2*r+1+(∑ x∈univ \ X,δ x) ≤ 2*G.edgeFinset.card+r*Q.card := by
    have pred := congrArg (Fintype.card V*·) (show r-1+1=r by omega)
    rw [Nat.mul_add,Nat.mul_one] at pred
    nlinarith only [all,ub,ecap,pred,xcount]
  refine ⟨Q,⟨disQ,clQ,?_⟩,arithmetic⟩
  have qsub : Q⊆P := filter_subset ..
  have qrank : ∑ A∈Q,rankOn G A=Q.card := by
    calc
      _ = ∑ _ ∈ Q,1 := sum_congr rfl fun A ha => le_antisymm (rank_clique_le_one G (clQ A ha).isClique)
        (hi _ (qsub ha)).rank_pos
      _ = _ := by simp
  have sub : univ \ X ⊆ (P\Q).biUnion id := by
    intro x hx
    have hxP : x∈P.biUnion id := hu ▸ mem_univ x
    obtain ⟨A,ha,hm⟩ := mem_biUnion.mp hxP
    exact mem_biUnion.mpr ⟨A,mem_sdiff.mpr ⟨ha,fun hq => (mem_sdiff.mp hx).2
      (mem_biUnion.mpr ⟨A,hq,hm⟩)⟩,hm⟩
  have le := (rankOn_mono G sub).trans (rankOn_biUnion_le G _)
  have eq := sum_sdiff qsub (f:=rankOn G)
  rw [hα,qrank] at eq
  change rankOn G (univ \ X)+Q.card ≤ r
  omega

/-- Every color of average degree at most r contains at least three disjoint
monochromatic r-cliques. The quantitative bound charges vertices outside the
packing for the shortfall of their local clique sizes from r−1. -/
theorem sparse_full_clique_packing (hr : 3≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (he : 2*(colorGraph c k).edgeFinset.card ≤ r*Fintype.card V) :
    ∃ Q : Finset (Finset V), 3≤Q.card ∧ FullCliqueRows c k Q ∧
      r*Fintype.card V+2*r+1+(∑ x∈univ \ Q.biUnion id,(r-1-pointClique (colorGraph c k) x)) ≤
        2*(colorGraph c k).edgeFinset.card+r*Q.card := by
  classical
  let G := colorGraph c k
  obtain ⟨P,hu,hd,hi,hα⟩ := exists_rank_partition G univ
  have cap : rankOn G univ ≤ r := (rankOn_univ_eq_indepNum G).le.trans (balanced_indepNum_le c hb k)
  have dense := rank_partition_density G P hd hi r
  rw [hu,card_univ,hn,blockEdges_univ,hα] at dense
  have parts : r≤2*P.card := rank_parts_of_edge_budget (e:=G.edgeFinset.card) hr (by simpa [G,hn] using he)
    (dense.trans (by have := Nat.mul_le_mul_left (r.choose 2+1) cap; omega))
  obtain ⟨Q,hQ,arithmetic⟩ := full_packing_on_partition hr hn c hb k P hu hd hi hα (by omega)
  refine ⟨Q,?_,hQ,arithmetic⟩
  change _ ≤ 2*G.edgeFinset.card+r*Q.card at arithmetic
  change 2*G.edgeFinset.card ≤ r*Fintype.card V at he
  by_contra! few
  have tmp := Nat.mul_le_mul_left r (show Q.card≤2 by omega)
  omega


private theorem full_rows_edge_budget (hr : 5≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) :
    ∃ Q : Finset (Finset V), FullCliqueRows c k Q ∧
      r*Fintype.card V+2*r+1 ≤ 2*(colorGraph c k).edgeFinset.card+r*Q.card := by
  classical
  let G := colorGraph c k
  obtain ⟨P,hu,hd,hi,hα⟩ := exists_rank_partition G univ
  by_cases big : 2 ≤ P.card
  · obtain ⟨Q,hQ,ub⟩ := full_packing_on_partition (by omega) hn c hb k P hu hd hi hα big
    exact ⟨Q,hQ,(Nat.le_add_right ..).trans ub⟩
  have cap : rankOn G univ≤r := (rankOn_univ_eq_indepNum G).le.trans (balanced_indepNum_le c hb k)
  refine ⟨∅,⟨by simp,by simp,by simpa [G] using cap⟩,?_⟩
  have dense := rank_partition_density G P hd hi r
  rw [hu,card_univ,hn,blockEdges_univ,hα] at dense
  have ca := Nat.mul_le_mul_left (r.choose 2+1) cap
  have cb := Nat.mul_le_mul_left (r-1) (show P.card≤1 by omega)
  rw [Nat.mul_one] at cb
  have eq := congrArg (r*·) (twice_choose_two r)
  change r*Fintype.card V+2*r+1 ≤ 2*G.edgeFinset.card+r*(∅ : Finset (Finset V)).card
  rw [card_empty,Nat.mul_zero,Nat.add_zero,hn]
  obtain ⟨u,eu⟩ := Nat.exists_eq_add_of_le hr
  have pred : r-1+1=r := by omega
  nlinarith only [dense,ca,cb,eq,congrArg ((r*r)*·) pred,pred,congrArg (·^2) eu,eu,Nat.zero_le (u^2),Nat.zero_le u]

/-- Across the palette there are at least 2r+1 monochromatic cliques of
order r. Rows of one color are pairwise disjoint. Rows in different colors
meet in precisely one vertex, and each family's complement loses one unit
of independence for every row removed. -/
theorem exists_transversal_full_rows (hr : 5≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ Q : Fin r → Finset (Finset V), (∀ k, FullCliqueRows c k (Q k)) ∧
      2*r+1 ≤ ∑ k,(Q k).card ∧
      ∀ i j : Fin r, i≠j → ∀ A∈Q i, ∀ B∈Q j,(A∩B).card=1 := by
  classical
  choose Q hQ count using full_rows_edge_budget hr hn c hb
  refine ⟨Q,hQ,?_,?_⟩
  · have total := sum_le_sum (s:=univ) fun k _ => count k
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum,card_univ,Fintype.card_fin,
      Nat.cast_id,sum_color_edges] at total
    have pairs := twice_choose_two (Fintype.card V)
    by_contra! few
    have le := Nat.mul_le_mul_left r (show (∑ k,(Q k).card)≤2*r by omega)
    nlinarith only [total,le,pairs,hr,congrArg (Fintype.card V*·) hn]
  · intro i j ne A ha B hB
    have indep : (colorGraph c j).IsNIndepSet r A :=
      ⟨fun _ hx _ hy hn edge => ne ((((hQ i).full A ha).isClique hx hy hn).2.symm.trans edge.2),
       ((hQ i).full A ha).card_eq⟩
    exact ((hQ j).transversal indep).2 B hB

/-- Every full clique in every color contains a vertex lying on full
cliques of at least three distinct colors. -/
theorem triple_point_on_every_full_clique (hr : 5≤r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) {C : Finset V}
    (hc : (colorGraph c k).IsNClique r C) : ∃ x∈C,3≤(fullColors c x).card := by
  classical
  obtain ⟨Q,hQ,total,_⟩ := exists_transversal_full_rows hr hn c hb
  let J := univ.erase k
  let U (j : Fin r) := (Q j).biUnion id
  have num (j : Fin r) (hj : j∈J) : (C.filter fun x => x∈U j).card=(Q j).card := by
    have indep : (colorGraph c j).IsNIndepSet r C :=
      ⟨fun _ hx _ hy ne edge => (mem_erase.mp hj).1 (edge.2.symm.trans (hc.isClique hx hy ne).2),hc.card_eq⟩
    have one := ((hQ j).transversal indep).2
    have dis : (↑(Q j) : Set (Finset V)).PairwiseDisjoint (fun B => C∩B) :=
      fun _ ha _ hb ne => ((hQ j).disjoint ha hb ne).mono inter_subset_right inter_subset_right
    rw [show (C.filter fun x => x∈U j)=C∩U j by ext; simp]
    change (C∩(Q j).biUnion id).card=_
    rw [inter_biUnion]
    simp only [id_eq]
    rw [card_biUnion dis,sum_congr rfl one]
    simp
  let F (x : V) := J.filter fun j => x∈U j
  have cross : ∑ x∈C,(F x).card = ∑ j∈J,(C.filter fun x => x∈U j).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun x j => x∈U j)
  rw [sum_congr rfl num] at cross
  have sub (x : V) (hx : x∈C) : (F x).card+1≤(fullColors c x).card := by
    have hk : k∉F x := fun h => (mem_erase.mp (mem_filter.mp h).1).1 rfl
    rw [←card_insert_of_notMem hk]
    apply card_le_card
    apply insert_subset ((mem_fullColors ..).mpr ⟨C,hx,hc⟩)
    intro j hj
    obtain ⟨B,ha,hxB⟩ := mem_biUnion.mp (mem_filter.mp hj).2
    exact (mem_fullColors ..).mpr ⟨B,hxB,(hQ j).full B ha⟩
  by_contra! few
  have all := sum_le_sum (s:=C) (g:=fun _ => 1) fun x hx => (by have := sub x hx; have := few x hx; omega : (F x).card≤1)
  rw [cross] at all
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,hc.card_eq] at all
  have eq := sum_erase_add univ (fun i => (Q i).card) (mem_univ k)
  change (∑ j∈J,(Q j).card)+(Q k).card = _ at eq
  have := (hQ k).residual
  omega

end Erdos617
