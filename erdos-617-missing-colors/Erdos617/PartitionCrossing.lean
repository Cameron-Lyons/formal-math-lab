module

public import Erdos617.ClusterExtension
public import Erdos617.SparseTransversal
public import Erdos617.RankEdges

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] {r m : ℕ}
  {c : Sym2 V → Fin r} {k : Fin r}

/-- If all r clique parts are close to full, many edges of their color must
cross between parts. Otherwise every outside vertex needs an almost complete
neighborhood in some part, exceeding the total room for such vertices. -/
theorem clique_partition_cross_floor (hι : Fintype.card ι=r) (hn : Fintype.card V=r^2+1)
    (hb : Balanced c) (P : ι → Finset V) {U : Finset V} (cover : univ.biUnion P=U)
    (dis : Pairwise fun i j => Disjoint (P i) (P j)) (cl : ∀ i,(colorGraph c k).IsClique (P i : Set V))
    (size : ∀ i,(P i).card≤r) (hm : 0<m)
    (few : ∀ i, (r-(P i).card+1)*(m-1)+(r-(P i).card+1).choose 2 < r-1)
    (F : Finset (Sym2 V)) (between : ∀ i j, i≠j → ∀ x∈P i, ∀ y∈P j,
      (colorGraph c k).Adj x y → s(x,y)∈F) : m^2≤F.card := by
  classical
  by_contra! small
  let G := colorGraph c k
  let W (i : ι) := Uᶜ.filter (fun z => ((P i).filter fun x => ¬G.Adj z x).card≤m-1)
  have inside (i : ι) : P i⊆U := cover ▸ subset_biUnion_of_mem P (mem_univ i)
  have paid (i : ι) : (W i).card ≤ r-(P i).card := by
    apply near_neighbors_of_large_clique hb (few i) (P i) (W i) (Nat.add_sub_of_le (size i)) (cl i)
    · exact Finset.disjoint_left.mpr fun x hx hW => (mem_compl.mp (mem_filter.mp hW).1) (inside i hx)
    · exact fun _ hz => (mem_filter.mp hz).2
  have outside : Uᶜ⊆univ.biUnion W := by
    intro z hz
    by_contra none
    let X (i : ι) := (P i).filter (fun x => ¬G.Adj z x)
    have enough (i : ι) : m≤(X i).card := by
      by_contra! few
      exact none (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨hz,by change (X i).card≤m-1; omega⟩⟩)
    obtain ⟨f,has,non⟩ := sparse_independent_transversal G X (fun i j ne => (dis ne).mono (filter_subset ..) (filter_subset ..))
      F hm enough (fun i j ne x hx y hy => between i j ne x (mem_filter.mp hx).1 y (mem_filter.mp hy).1) small
    have inj : Function.Injective f := by
      intro i j eq
      by_contra ne
      exact Finset.disjoint_left.mp (dis ne) (mem_filter.mp (has i)).1 (eq ▸ (mem_filter.mp (has j)).1)
    let I := univ.image f
    have ind : G.IsIndepSet (I : Set V) := by
      intro x hx y hy ne
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp hy
      exact non i j (fun eq => ne (congrArg f eq))
    have noZ : z∉I := by
      intro h
      obtain ⟨i,_,eq⟩ := mem_image.mp h
      exact mem_compl.mp hz (eq ▸ inside i (mem_filter.mp (has i)).1)
    have larger := independent_insert_of_nonadjacent G ind z (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp (has i)).2)
    have order : (insert z I).card=r+1 := by simp [I,card_insert_of_notMem noZ,card_image_of_injective _ inj,hι]
    obtain ⟨x,hx,y,hy,ne,col⟩ := hb _ order k
    exact larger hx hy ne ⟨ne,col⟩
  have outcard := (card_le_card outside).trans card_biUnion_le
  have count := card_biUnion (s:=univ) (t:=P) (fun _ _ _ _ ne => dis ne)
  rw [cover] at count
  have total := sum_le_sum (s:=univ) fun i _ => paid i
  have payments := sum_congr (s₁:=univ) rfl fun i _ => Nat.sub_add_cancel (size i)
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,hι,Nat.cast_id,←pow_two] at payments
  have order : Uᶜ.card+U.card=r^2+1 := (card_compl_add_card U).trans hn
  omega

/-- In an equipartition of the smaller square into r cliques, cross edges
alone cost at least the square of the integer part of (r−2)/3. -/
theorem square_equipartition_cross_floor {U : Finset V} (hr : 5≤r) (hι : Fintype.card ι=r)
    (hn : Fintype.card V=r^2+1) (hb : Balanced c) (P : ι → Finset V)
    (cover : univ.biUnion P=U) (dis : Pairwise fun i j => Disjoint (P i) (P j))
    (cl : ∀ i,(colorGraph c k).IsClique (P i : Set V))
    (sizes : ∀ i,(P i).card=r-2 ∨ (P i).card=r-1) (F : Finset (Sym2 V))
    (between : ∀ i j,i≠j → ∀ x∈P i, ∀ y∈P j,(colorGraph c k).Adj x y → s(x,y)∈F) :
    ((r-2)/3)^2≤F.card := by
  apply clique_partition_cross_floor hι hn hb P cover dis cl (fun i => by have := sizes i; omega) (by omega) _ F between
  intro i
  rcases sizes i with e|e
  · rw [e,show r-(r-2)+1=3 by omega]
    norm_num [Nat.choose]
    omega
  · rw [e,show r-(r-1)+1=2 by omega]
    norm_num [Nat.choose]
    omega

end Erdos617
