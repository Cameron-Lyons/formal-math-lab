module

public import Erdos617.RankSquareProfile

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

private theorem score_clean_rows {n r b h : ℕ} (hr : 6≤r) (hn : n≤r)
    (o p : Fin n → ℕ) (caps : ∀ i,o i≤r-1)
    (sh : (∑ i, (r-1-o i)) ≤ h)
    (loss : (∑ i, (o i-p i)) ≤ (b+1)*(r-2)) :
    (∑ i, if o i=r-1 ∧ 2*(o i-p i)+1<r-1 then 1 else 4) ≤ r+3*h+6*(b+1) := by
  classical
  let A := univ.filter fun i => o i≠r-1
  let B := univ.filter fun i => r-1≤2*(o i-p i)+1
  have asmall : A.card≤h := by
    have per := sum_le_sum (s:=A) (f:=fun _ => 1) (g:=fun i => r-1-o i) (fun i hi => by
      have := (mem_filter.mp hi).2
      have := caps i
      omega)
    have all := sum_le_sum_of_subset_of_nonneg (subset_univ A) (f:=fun i => r-1-o i) (by simp)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at per
    omega
  have bsmall : B.card≤2*(b+1) := by
    have per := sum_le_sum (s:=B) (f:=fun _ => r-2) (g:=fun i => 2*(o i-p i)) (fun i hi => by
      have := (mem_filter.mp hi).2
      omega)
    have all := sum_le_sum_of_subset_of_nonneg (subset_univ B) (f:=fun i => o i-p i) (by simp)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,←mul_sum] at per
    apply Nat.le_of_mul_le_mul_right (c:=r-2) ?_ (by omega : 0<r-2)
    nlinarith only [per,all,loss]
  have per : ∀ i∈(univ : Finset (Fin n)), (if o i=r-1 ∧ 2*(o i-p i)+1<r-1 then 1 else 4) ≤
      1+3*(if i∈A then 1 else 0)+3*(if i∈B then 1 else 0) := by
    intro i _
    simp only [A,B,mem_filter,mem_univ,true_and]
    split_ifs <;> omega
  have sum := sum_le_sum per
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_univ,Fintype.card_fin,
    ←mul_sum,sum_boole,filter_mem_eq_inter,univ_inter] at sum
  omega

/-- Outside endpoints of crossing edges can be removed without disturbing a
chosen maximum independent set. Each rank-one part retains a vertex of it. -/
private theorem clean_given_rank_rows {r b h : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 6≤r) (U : Finset V)
    (Q R : Finset (Finset V)) (hu : Q.biUnion id=U)
    (hd : (↑Q : Set (Finset V)).PairwiseDisjoint id)
    (hs : ∑ A∈Q,rankOn G A=rankOn G U) (rankU : rankOn G U=r-1)
    (subR : R⊆Q) (one : ∀ A∈R,rankOn G A=1) (cap : ∀ A∈R,A.card≤r-1)
    (nr : r-1≤R.card+2*(b+1))
    (sh : (∑ A∈R,(r-1-A.card))≤h)
    (few : (inducedEdgeSet G U \ Q.biUnion (inducedEdgeSet G)).card ≤ (b+1)*(r-2)) :
    ∃ (n : ℕ) (J : Finset V) (P O : Fin n → Finset V), J⊆U ∧ G.IsIndepSet (J : Set V) ∧
      n+J.card=r-1 ∧ J.card≤2*(b+1) ∧
      (∀ i,O i⊆U ∧ G.IsClique (O i:Set V) ∧ (O i).card≤r-1 ∧ P i⊆O i ∧ (P i).Nonempty) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (∀ i,Disjoint (P i) J) ∧
      (∀ i j,i≠j → ∀ x∈P i,∀ y∈P j,¬G.Adj x y) ∧
      (∀ i,∀ x∈P i,∀ y∈J,¬G.Adj x y) ∧
      (∑ i, if (O i).card=r-1 ∧ 2*((O i).card-(P i).card)+1<r-1 then 1 else 4) ≤ r+3*h+6*(b+1) := by
  classical
  obtain ⟨I,subI,ind,nI⟩ := exists_max_indep G U
  have dint (M : Finset (Finset V)) (sub : M⊆Q) :
      (↑M : Set _).PairwiseDisjoint (fun A => I∩A) :=
    fun _ ha _ hb ne => (hd (sub ha) (sub hb) ne).mono inter_subset_right inter_subset_right
  have how (A : Finset V) (ha : A∈Q) : (I∩A).card≤rankOn G A :=
    card_le_rankOn G inter_subset_right (ind.mono inter_subset_left)
  have meet (A : Finset V) (ha : A∈Q) : (I∩A).card=rankOn G A := by
    apply (sum_eq_sum_iff_of_le how).mp _ A ha
    rw [←card_biUnion (dint Q (Subset.rfl)),hs,←nI]
    change (Q.biUnion (fun A => I∩id A)).card=I.card
    rw [←inter_biUnion,hu,inter_eq_left.mpr subI]
  let X := R.biUnion id
  let J := I \ X
  have coreSize : R.card+J.card=r-1 := by
    have count := card_biUnion (dint R subR)
    change (R.biUnion (fun A => I∩id A)).card=(∑ A∈R,(I∩A).card) at count
    rw [←inter_biUnion] at count
    rw [sum_congr rfl (fun A ha => (meet A (subR ha)).trans (one A ha))] at count
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at count
    have split : J.card+(I∩X).card=I.card := card_sdiff_add_card_inter I X
    change (I∩X).card=R.card at count
    omega
  let F := inducedEdgeSet G U \ Q.biUnion (inducedEdgeSet G)
  have outside (e : Sym2 V) (he : e∈F) : ∃ z : V,z∈e ∧ z∉I := by
    induction e using Sym2.inductionOn with | _ x y =>
      have a := ((mem_inducedEdgeSet G).mp (mem_sdiff.mp he).1).2.2
      by_cases inI : x∈I
      · exact ⟨y,by simp,fun hy => ind inI hy a.ne a⟩
      · exact ⟨x,by simp,inI⟩
  choose f fm fo using (fun e : F => outside e.val e.prop)
  let D := univ.image f
  have dc : D.card≤(b+1)*(r-2) := by
    have le : D.card≤(univ : Finset F).card := card_image_le
    simpa using le.trans (by simpa using few)
  have dI : Disjoint D I := by
    apply Finset.disjoint_left.mpr
    intro x hx
    obtain ⟨e,_,rfl⟩ := mem_image.mp hx
    exact fo e
  have inside (A : Finset V) (ha : A∈Q) : A⊆U := (biUnion_subset.mp hu.le) A ha
  have unique {A B : Finset V} (ha : A∈Q) (hb : B∈Q) {x : V} (hx : x∈A) (hx' : x∈B) : A=B :=
    by_contra (fun h => Finset.disjoint_left.mp (hd ha hb h) hx hx')
  have cross {A B : Finset V} (ha : A∈Q) (hb : B∈Q) (ne : A≠B) {x y : V} (hx : x∈A)
      (hy : y∈B) (e : G.Adj x y) : x∈D ∨ y∈D := by
    have he : s(x,y)∈F := by
      refine mem_sdiff.mpr ⟨(mem_inducedEdgeSet G).mpr ⟨inside _ ha hx,inside _ hb hy,e⟩,?_⟩
      intro internal
      obtain ⟨C,hc,edge⟩ := mem_biUnion.mp internal
      obtain ⟨xc,yc,_⟩ := (mem_inducedEdgeSet G).mp edge
      exact ne ((unique ha hc hx xc).trans (unique hc hb yc hy))
    let a : F := ⟨s(x,y),he⟩
    have del : f a∈D := mem_image_of_mem f (mem_univ a)
    rcases Sym2.mem_iff.mp (show f a∈s(x,y) from fm a) with eq | eq
    · exact Or.inl (eq ▸ del)
    · exact Or.inr (eq ▸ del)
  let rep : Fin R.card ≃ R := (Fintype.equivFinOfCardEq (Fintype.card_coe R)).symm
  let O (i : Fin R.card) := (rep i).val
  let P (i : Fin R.card) := O i \ D
  let L (i : Fin R.card) := O i ∩ D
  have memR (i) : O i∈R := (rep i).prop
  have memQ (i) : O i∈Q := subR (memR i)
  have diff {i j} (ne : i≠j) : O i≠O j := fun eq => ne (rep.injective (Subtype.ext eq))
  have subX (i) : O i⊆X := subset_biUnion_of_mem id (memR i)
  have pos (i) : (P i).Nonempty := by
    have n := (meet (O i) (memQ i)).trans (one _ (memR i))
    obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<(I∩O i).card)
    exact ⟨x,mem_sdiff.mpr ⟨(mem_inter.mp hx).2,Finset.disjoint_left.mp dI.symm (mem_inter.mp hx).1⟩⟩
  have lcap : (∑ i,((O i).card-(P i).card)) ≤ (b+1)*(r-2) := by
    have ld : (↑(univ : Finset (Fin R.card)) : Set _).PairwiseDisjoint L :=
      fun i _ j _ ne => (hd (memQ i) (memQ j) (diff ne)).mono inter_subset_left inter_subset_left
    have h := card_le_card (biUnion_subset.mpr (fun _ _ => inter_subset_right) : univ.biUnion L⊆D)
    rw [card_biUnion ld] at h
    have eq := sum_congr (s₁:=univ) rfl (fun i _ => (show (O i).card-(P i).card=(L i).card by
      have : (P i).card+(L i).card=(O i).card := card_sdiff_add_card_inter _ _
      omega))
    omega
  have shortage : (∑ i,(r-1-(O i).card))≤h := by
    change (∑ i,(fun A : R => r-1-A.val.card) (rep i))≤_
    rw [rep.sum_comp (fun A : R => r-1-A.val.card),Finset.sum_coe_sort R (fun A : Finset V => r-1-A.card)]
    exact sh
  have jsub : J⊆I := sdiff_subset
  refine ⟨R.card,J,P,O,jsub.trans subI,ind.mono jsub,coreSize,by omega,
    (fun i => ⟨inside _ (memQ i),rank_one_clique _ (one _ (memR i)),cap _ (memR i),sdiff_subset,pos i⟩),
    (fun i j ij => (hd (memQ i) (memQ j) (diff ij)).mono sdiff_subset sdiff_subset),?_,?_,?_,?_⟩
  · intro i
    exact Finset.disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hy).2 (subX i (mem_sdiff.mp hx).1))
  · intro i j ij x hx y hy e
    exact (cross (memQ i) (memQ j) (diff ij) (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 e).elim
      (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).2
  · intro i x hx y hy e
    have inQ : y∈Q.biUnion id := hu ▸ subI (jsub hy)
    obtain ⟨A,ha,ya⟩ := mem_biUnion.mp inQ
    have ne : O i≠A := fun eq => (mem_sdiff.mp hy).2 (subX i (eq ▸ ya))
    exact (cross (memQ i) ha ne (mem_sdiff.mp hx).1 ya e).elim (mem_sdiff.mp hx).2
      (fun yd => Finset.disjoint_left.mp dI yd (jsub hy))
  · exact score_clean_rows hr (by omega) _ _ (fun i => cap _ (memR i)) shortage lcap

/-- A low-cost good color on the smaller square has a fixed independent set
and separated nonempty remnants of large cliques carrying the remaining rank. -/
theorem clean_rank_witness_rows {r : ℕ}
    (c : Sym2 V → Fin r) (k : Fin r) (hr : 6≤r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (cap : rankOn (colorGraph c k) U≤r-1)
    (no : ∀ A⊆U, ¬(colorGraph c k).IsNClique r A) {b : ℕ}
    (large : 1000*(2*(b+1))^2<r)
    (budget : blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+b*(r-2)) :
    let G := colorGraph c k
    ∃ (n : ℕ) (J : Finset V) (P O : Fin n → Finset V), J⊆U ∧ G.IsIndepSet (J : Set V) ∧
      n+J.card=r-1 ∧ J.card≤2*(b+1) ∧
      (∀ i,O i⊆U ∧ G.IsClique (O i:Set V) ∧ (O i).card≤r-1 ∧ P i⊆O i ∧ (P i).Nonempty) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (∀ i,Disjoint (P i) J) ∧
      (∀ i j,i≠j → ∀ x∈P i,∀ y∈P j,¬G.Adj x y) ∧
      (∀ i,∀ x∈P i,∀ y∈J,¬G.Adj x y) ∧
      (∑ i, if (O i).card=r-1 ∧ 2*((O i).card-(P i).card)+1<r-1 then 1 else 4) ≤ r+12*(b+1) := by
  classical
  let G := colorGraph c k
  obtain ⟨Q,hu,hd,_,s,rk,data,few⟩ := square_rank_profile c k hr hb U sz cap no large budget
  let R := Q.filter fun A => rankOn G A=1
  obtain ⟨mass,small,caps,sh,_⟩ := data
  have result := clean_given_rank_rows G hr U Q R hu hd (s.trans rk.symm) rk (filter_subset ..)
    (fun _ h => (mem_filter.mp h).2) caps (mass.ge.trans (Nat.add_le_add_left small _)) sh
    (few.trans (Nat.mul_le_mul_right _ (Nat.le_succ b)))
  simpa only [show r+3*(2*(b+1))+6*(b+1)=r+12*(b+1) by omega] using result

/-- A low-cost good color on the smaller square has a fixed independent set
and separated nonempty remnants of large cliques carrying the remaining rank. -/
theorem clean_rank_witness_rows_linear {r : ℕ}
    (c : Sym2 V → Fin r) (k : Fin r) (hr : 6≤r) (hb : Balanced c)
    (U : Finset V) (sz : U.card=(r-1)^2+1) (cap : rankOn (colorGraph c k) U≤r-1)
    (no : ∀ A⊆U, ¬(colorGraph c k).IsNClique r A) {b : ℕ}
    (large : 6*(b+1)<r)
    (budget : blockEdges (colorGraph c k) U≤(r-1)*(r-1).choose 2+2*(r-1)-1+b*(r-2)) :
    let G := colorGraph c k
    ∃ (n : ℕ) (J : Finset V) (P O : Fin n → Finset V), J⊆U ∧ G.IsIndepSet (J : Set V) ∧
      n+J.card=r-1 ∧ J.card≤2*(b+1) ∧
      (∀ i,O i⊆U ∧ G.IsClique (O i:Set V) ∧ (O i).card≤r-1 ∧ P i⊆O i ∧ (P i).Nonempty) ∧
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (∀ i,Disjoint (P i) J) ∧
      (∀ i j,i≠j → ∀ x∈P i,∀ y∈P j,¬G.Adj x y) ∧
      (∀ i,∀ x∈P i,∀ y∈J,¬G.Adj x y) ∧
      (∑ i, if (O i).card=r-1 ∧ 2*((O i).card-(P i).card)+1<r-1 then 1 else 4) ≤ r+24*(b+1) := by
  classical
  let G := colorGraph c k
  obtain ⟨Q,hu,hd,_,s,rk,data,few⟩ := square_rank_soft_profile c k hr hb U sz cap no large budget
  let R := Q.filter fun A => rankOn G A=1
  obtain ⟨mass,small,caps,sh⟩ := data
  have result := clean_given_rank_rows G hr U Q R hu hd (s.trans rk.symm) rk (filter_subset ..)
    (fun _ h => (mem_filter.mp h).2) caps (mass.ge.trans (Nat.add_le_add_left small _)) sh
    (few.trans (Nat.mul_le_mul_right _ (Nat.le_succ b)))
  simpa only [show r+3*(6*(b+1))+6*(b+1)=r+24*(b+1) by omega] using result

end Erdos617
