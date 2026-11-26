module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Data.Finset.Sum

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private structure MatchingCut (G : SimpleGraph V) where
  removed : Finset V
  blocks : Finset (Finset V)
  cover : blocks.biUnion id = univ \ removed
  disjoint : (↑blocks : Set (Finset V)).PairwiseDisjoint id
  nonempty : ∀ A ∈ blocks, A.Nonempty
  links : ∀ x y, x ∉ removed → y ∉ removed → G.Adj x y → ∃ A ∈ blocks, x ∈ A ∧ y ∈ A

/-- Project the connected components given by a Tutte violator back to the
original vertex type and sum the contribution of their odd orders. -/
private theorem cut_of_violator (G : SimpleGraph V) (u : Set V) (hu : G.IsTutteViolator u) :
    ∃ C : MatchingCut G, 2*(C.removed.card+∑ A ∈ C.blocks,A.card/2) < Fintype.card V := by
  classical
  let R := (⊤ : G.Subgraph).deleteVerts u
  let H := R.coe
  let Q (K : H.ConnectedComponent) := K.supp.toFinset.map (Function.Embedding.subtype (· ∈ R.verts))
  let U := u.toFinset
  let P := univ.image Q
  have memQ (K : H.ConnectedComponent) (x : R.verts) : x.val ∈ Q K ↔ H.connectedComponentMk x = K := by
    simp [Q,ConnectedComponent.mem_supp_iff]
  have sub (K : H.ConnectedComponent) {x : V} (hx : x ∈ Q K) : x ∈ R.verts := by
    obtain ⟨v,_,rfl⟩ := mem_map.mp hx
    exact v.prop
  have nonempty (K : H.ConnectedComponent) : (Q K).Nonempty :=
    ⟨K.out.val, (memQ _ _).mpr K.out_eq⟩
  have inj : Function.Injective Q := by
    intro A B he
    have hx := (memQ A A.out).mpr A.out_eq
    rw [he] at hx
    exact A.out_eq.symm.trans ((memQ _ _).mp hx)
  have hsub {x : V} : x∈R.verts ↔ x∉U := by simp [R,U]
  have cover : P.biUnion id = univ \ U := by
    ext x
    constructor
    · intro hx
      obtain ⟨A,hA,hx⟩ := mem_biUnion.mp hx
      obtain ⟨K,_,rfl⟩ := mem_image.mp hA
      exact mem_sdiff.mpr ⟨mem_univ _,hsub.mp (sub K hx)⟩
    · intro hx
      let v : R.verts := ⟨x,hsub.mpr (mem_sdiff.mp hx).2⟩
      exact mem_biUnion.mpr ⟨Q (H.connectedComponentMk v),mem_image_of_mem Q (mem_univ _),
        (memQ _ v).mpr rfl⟩
  have dis : (↑P : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB hab
    obtain ⟨K,_,rfl⟩ := mem_image.mp hA
    obtain ⟨L,_,rfl⟩ := mem_image.mp hB
    refine disjoint_left.mpr fun x hx hy => ?_
    let v := (⟨x,sub K hx⟩ : R.verts)
    exact hab (congrArg Q (((memQ _ v).mp hx).symm.trans ((memQ _ v).mp hy)))
  have link (x y : V) (hx : x∉U) (hy : y∉U) (he : G.Adj x y) :
      ∃ A ∈ P, x ∈ A ∧ y ∈ A := by
    let v := (⟨x,hsub.mpr hx⟩ : R.verts)
    let w := (⟨y,hsub.mpr hy⟩ : R.verts)
    have adj : H.Adj v w := Subgraph.deleteVerts_adj.mpr ⟨Set.mem_univ _,(hsub.mpr hx).2,
      Set.mem_univ _,(hsub.mpr hy).2,he⟩
    exact ⟨_,mem_image_of_mem Q (mem_univ (H.connectedComponentMk v)),(memQ _ v).mpr rfl,
      (memQ _ w).mpr (ConnectedComponent.eq.mpr adj.reachable.symm)⟩
  refine ⟨⟨U,P,cover,dis,fun A hA => by obtain ⟨K,_,rfl⟩ := mem_image.mp hA; exact nonempty K,
    link⟩,?_⟩
  change 2*(U.card+∑ A ∈ P,A.card/2)<Fintype.card V
  have HC := card_biUnion dis
  rw [cover,card_sdiff_of_subset (subset_univ _),card_univ] at HC
  simp only [id_eq] at HC
  have Hle := card_le_univ U
  have ord (K : H.ConnectedComponent) : (Q K).card=K.supp.ncard := by
    simp only [Q,card_map,Set.ncard_eq_toFinset_card']
  have odds : (∑ K : H.ConnectedComponent, (Q K).card%2) = H.oddComponents.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    have eq : H.oddComponents.toFinset = univ.filter (fun K : H.ConnectedComponent => Odd (Q K).card) := by
      ext K
      simp [oddComponents,ord]
    rw [eq,Finset.card_filter]
    apply sum_congr rfl
    intro K _
    split <;> rename_i h
    · exact Nat.odd_iff.mp h
    · have hn : (Q K).card%2 ≠ 1 := fun hh => h (Nat.odd_iff.mpr hh)
      omega
  have ident : (∑ K : H.ConnectedComponent, (2*((Q K).card/2)+(Q K).card%2)) =
      ∑ K : H.ConnectedComponent, (Q K).card :=
    sum_congr rfl fun K _ => by omega
  rw [sum_add_distrib,←mul_sum,odds] at ident
  dsimp [P] at HC ⊢
  rw [sum_image inj.injOn] at HC ⊢
  change u.ncard < H.oddComponents.ncard at hu
  rw [Set.ncard_eq_toFinset_card' u] at hu
  change U.card < H.oddComponents.ncard at hu
  omega

/-- The additional labels are adjacent to every other vertex. -/
private def padGraph (G : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj x y := match x,y with
    | .inl a,.inl b => G.Adj a b
    | .inr a,.inr b => a≠b
    | .inl _,.inr _ | .inr _,.inl _ => True
  symm := ⟨by rintro (a|a) (b|b) h <;> first | exact h.symm | trivial⟩
  loopless := ⟨by rintro (a|a) <;> first | exact G.loopless.irrefl a | exact fun h => h rfl⟩

private theorem matching_of_padded_perfect (G : SimpleGraph V) (d : ℕ)
    (M : (padGraph G d).Subgraph) (hm : M.IsPerfectMatching) :
    ∃ F : Finset (Sym2 V), (∀ e ∈ F,e ∈ G.edgeSet) ∧
      (↑F : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset ∧ Fintype.card V ≤ 2*F.card+d := by
  classical
  choose mate hmAdj _ using Subgraph.isPerfectMatching_iff.mp hm
  let F := univ.filter (fun e : Sym2 V => e.map Sum.inl ∈ M.edgeSet)
  have edge {a b : V} : s(a,b) ∈ F ↔ M.Adj (.inl a) (.inl b) := by
    simp [F]
  have actual (e : Sym2 V) (he : e ∈ F) : e∈G.edgeSet := by
    induction e using Sym2.inductionOn with
    | _ a b => exact (edge.mp he).adj_sub
  have dis : (↑F : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e he g hg hne
    refine disjoint_left.mpr fun x hx hy => ?_
    obtain ⟨a,rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx)
    obtain ⟨b,rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hy)
    exact hne (congrArg (s(x,·)) (Sum.inl.inj (hm.1.eq_of_adj_right (edge.mp he).symm (edge.mp hg).symm)))
  let D := (univ.image (fun i : Fin d => mate (.inr i))).toLeft
  have hD : D.card ≤ d :=
    card_toLeft_le.trans (card_image_le.trans (by simp))
  have all : (univ : Finset V) ⊆ F.biUnion Sym2.toFinset ∪ D := by
    intro x _
    cases h : mate (.inl x) with
    | inl y =>
      have he := hmAdj (.inl x)
      rw [h] at he
      exact mem_union_left _ (mem_biUnion.mpr ⟨s(x,y),edge.mpr he,Sym2.mem_toFinset.mpr (Sym2.mem_mk_left ..)⟩)
    | inr j =>
      have he := hmAdj (.inl x)
      rw [h] at he
      have hj := hm.1.eq_of_adj_right (hmAdj (.inr j)).symm he
      exact mem_union_right _ (mem_toLeft.mpr (mem_image.mpr ⟨j,mem_univ _,hj⟩))
  have card := (card_le_card all).trans (card_union_le _ _)
  rw [card_univ,card_biUnion dis] at card
  have cs : (∑ e ∈ F,e.toFinset.card) = 2*F.card := by
    rw [sum_congr rfl (g := fun _ => 2) (fun e he => Sym2.card_toFinset_of_not_isDiag _
      (G.not_isDiag_of_mem_edgeSet (actual e he)))]
    simp [Nat.mul_comm]
  exact ⟨F,actual,dis,by omega⟩

private theorem unpad_cut (G : SimpleGraph V) (d t : ℕ) (hn : Fintype.card V=d+2*t+2)
    (C : MatchingCut (padGraph G d))
    (hcost : 2*(C.removed.card+∑ A ∈ C.blocks,A.card/2) < Fintype.card (V ⊕ Fin d)) :
    ∃ B : MatchingCut G, B.removed.card+(∑ A ∈ B.blocks,A.card/2) ≤ t := by
  classical
  rw [Fintype.card_sum,Fintype.card_fin] at hcost
  have sub {A : Finset (V ⊕ Fin d)} (hA : A ∈ C.blocks) : A ⊆ univ \ C.removed :=
    (biUnion_subset.mp C.cover.le) _ hA
  have unique {A B : Finset (V ⊕ Fin d)} (hA : A ∈ C.blocks) (hB : B ∈ C.blocks)
      {x} (hx : x ∈ A) (hy : x ∈ B) : A=B := by
    by_contra h
    exact disjoint_left.mp (C.disjoint hA hB h) hx hy
  have dummy (z : Fin d) : Sum.inr z ∈ C.removed := by
    by_contra hz
    have hz' : Sum.inr z ∈ C.blocks.biUnion id := C.cover ▸ mem_sdiff.mpr ⟨mem_univ _,hz⟩
    obtain ⟨B,hB,hzB⟩ := mem_biUnion.mp hz'
    have single : C.blocks = {B} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hB,fun A hA => ?_⟩
      obtain ⟨x,hx⟩ := C.nonempty A hA
      by_cases h : x=.inr z
      · exact unique hA hB hx (h ▸ hzB)
      have adj : (padGraph G d).Adj x (.inr z) := by
        cases x with
        | inl => trivial
        | inr v => exact fun eq => h (congrArg _ eq)
      obtain ⟨K,hK,hxK,hzK⟩ := C.links _ _ (mem_sdiff.mp (sub hA hx)).2 hz adj
      exact (unique hA hK hx hxK).trans (unique hK hB hzK hzB)
    have full := C.cover
    rw [single] at full hcost
    simp only [singleton_biUnion,id_eq] at full
    simp only [sum_singleton] at hcost
    have n := card_sdiff_add_card_eq_card (subset_univ C.removed)
    rw [←full,card_univ,Fintype.card_sum,Fintype.card_fin] at n
    omega
  have emptyR {A : Finset (V ⊕ Fin d)} (hA : A∈C.blocks) : A.toRight = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact (mem_sdiff.mp (sub hA (mem_toRight.mp hz))).2 (dummy z)
  have cardL {A : Finset (V ⊕ Fin d)} (hA : A∈C.blocks) : A.toLeft.card = A.card := by
    have hh := card_toLeft_add_card_toRight (u := A)
    simpa [emptyR hA] using hh
  have inj : Set.InjOn Finset.toLeft (↑C.blocks : Set (Finset (V ⊕ Fin d))) := by
    intro A hA B hB he
    rw [← toLeft_disjSum_toRight (u := A),← toLeft_disjSum_toRight (u := B),he,emptyR hA,emptyR hB]
  let P := C.blocks.image Finset.toLeft
  let U := C.removed.toLeft
  have cover : P.biUnion id = univ \ U := by
    ext x
    constructor
    · intro hx
      obtain ⟨A,hA,hx⟩ := mem_biUnion.mp hx
      obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
      exact mem_sdiff.mpr ⟨mem_univ _,fun hy => (mem_sdiff.mp (sub hB (mem_toLeft.mp hx))).2
        (mem_toLeft.mp hy)⟩
    · intro hx
      have hz : .inl x ∈ C.blocks.biUnion id := C.cover ▸
        mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_sdiff.mp hx).2 (mem_toLeft.mpr h)⟩
      obtain ⟨B,hB,hx⟩ := mem_biUnion.mp hz
      exact mem_biUnion.mpr ⟨B.toLeft,mem_image_of_mem _ hB,mem_toLeft.mpr hx⟩
  have dis : (↑P : Set (Finset V)).PairwiseDisjoint id := by
    intro A hA B hB h
    obtain ⟨X,hX,rfl⟩ := mem_image.mp hA
    obtain ⟨Y,hY,rfl⟩ := mem_image.mp hB
    exact disjoint_left.mpr fun x hx hy => h (congrArg Finset.toLeft (unique hX hY
      (mem_toLeft.mp hx) (mem_toLeft.mp hy)))
  have nonempty (A : Finset V) (hA : A∈P) : A.Nonempty := by
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
    exact card_pos.mp ((cardL hB).symm ▸ card_pos.mpr (C.nonempty B hB))
  have links (x y : V) (hx : x∉U) (hy : y∉U) (he : G.Adj x y) :
      ∃ A ∈ P, x ∈ A ∧ y ∈ A := by
    obtain ⟨B,hB,xB,yB⟩ := C.links (.inl x) (.inl y) (fun h => hx (mem_toLeft.mpr h))
      (fun h => hy (mem_toLeft.mpr h)) he
    exact ⟨_,mem_image_of_mem _ hB,mem_toLeft.mpr xB,mem_toLeft.mpr yB⟩
  refine ⟨⟨U,P,cover,dis,nonempty,links⟩,?_⟩
  change U.card+(∑ A ∈ P,A.card/2) ≤ t
  have sum : (∑ A ∈ P,A.card/2) = ∑ A ∈ C.blocks,A.card/2 := by
    dsimp [P]
    rw [sum_image inj]
    exact sum_congr rfl fun A hA => congrArg (· / 2) (cardL hA)
  have allR : C.removed.toRight = univ := eq_univ_iff_forall.mpr fun z => mem_toRight.mpr (dummy z)
  have count := card_toLeft_add_card_toRight (u := C.removed)
  rw [allR,card_univ,Fintype.card_fin] at count
  dsimp [U]
  omega

/-- A Tutte–Berge certificate for an upper bound on the matching number.
All edges left by the deleted vertices are internal to the displayed blocks. -/
theorem matching_certificate (G : SimpleGraph V) (t : ℕ)
    (hcap : ∀ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G.edgeSet) →
      (↑F : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset → F.card ≤ t) :
    ∃ (U : Finset V) (P : Finset (Finset V)), P.biUnion id = univ \ U ∧
      (↑P : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ x y, x ∉ U → y ∉ U → G.Adj x y → ∃ A ∈ P, x ∈ A ∧ y ∈ A) ∧
      U.card+(∑ A ∈ P,A.card/2) ≤ t := by
  classical
  by_cases hsmall : Fintype.card V ≤ 2*t+1
  · refine ⟨∅,{univ},by simp,by simp,fun x y _ _ _ => ⟨univ,by simp,mem_univ _,mem_univ _⟩,?_⟩
    simp only [card_empty,sum_singleton,card_univ,Nat.zero_add]
    omega
  let d := Fintype.card V - (2*t+2)
  have hn : Fintype.card V = d+2*t+2 := by dsimp [d]; omega
  have even : Even (Nat.card (V ⊕ Fin d)) := by
    rw [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_fin]
    exact ⟨d+t+1,by omega⟩
  have none (M : (padGraph G d).Subgraph) : ¬M.IsPerfectMatching := by
    intro perfect
    obtain ⟨F,he,hd,hc⟩ := matching_of_padded_perfect G d M perfect
    have := hcap F he hd
    omega
  obtain ⟨v,hv⟩ := SimpleGraph.exists_isTutteViolator none even
  obtain ⟨C,hC⟩ := cut_of_violator _ v hv
  obtain ⟨B,hB⟩ := unpad_cut G d t hn C hC
  exact ⟨B.removed,B.blocks,B.cover,B.disjoint,B.links,hB⟩

end Erdos617
