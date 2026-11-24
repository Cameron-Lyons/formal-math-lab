import Erdos617.MatchingCertificate
import Erdos617.LocalPaletteEnergy

namespace Erdos617

open SimpleGraph Finset

/-- If a single color is the union of two partitions into cliques, a balanced
r-coloring has at most r² vertices. Repeated pairs of class labels are allowed. -/
theorem balanced_two_partitions_bound {V A D : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [Fintype D] {r : ℕ} (hr : 2≤r) (c : Sym2 V → Fin r) (hb : Balanced c)
    (k : Fin r) (p : V → A) (q : V → D)
    (repr : ∀ x y, x≠y → (c s(x,y)=k ↔ p x=p y ∨ q x=q y)) :
    Fintype.card V≤r^2 := by
  classical
  let L := A ⊕ D
  let pts (x : V) : Sym2 L := s(Sum.inl (p x),Sum.inr (q x))
  let G : SimpleGraph L := fromEdgeSet (↑(univ.image pts) : Set (Sym2 L))
  obtain ⟨j,hj⟩ : (univ.erase k).Nonempty := card_pos.mp (by simp; omega)
  let lines (l : L) : Finset V := univ.filter fun x => l∈(pts x).toFinset
  have lineCap (l : L) : (lines l).card≤r := by
    have ind : (colorGraph c j).IsIndepSet (lines l : Set V) := by
      intro x hx y hy xy edge
      have xl := (mem_filter.mp (show x∈lines l from hx)).2
      have yl := (mem_filter.mp (show y∈lines l from hy)).2
      have same : p x=p y ∨ q x=q y := by
        cases l with
        | inl a =>
          simp [pts,Sym2.toFinset_mk_eq] at xl yl
          exact Or.inl (Sum.inl.inj (xl.symm.trans yl))
        | inr b =>
          simp [pts,Sym2.toFinset_mk_eq] at xl yl
          exact Or.inr (Sum.inr.inj (xl.symm.trans yl))
      exact (mem_erase.mp hj).1 (edge.2.symm.trans ((repr x y xy).mpr same))
    exact ind.card_le_indepNum.trans (balanced_indepNum_le c hb j)
  have matchCap (F : Finset (Sym2 L)) (he : ∀ e∈F,e∈G.edgeSet)
      (hd : (↑F : Set (Sym2 L)).PairwiseDisjoint Sym2.toFinset) : F.card≤r := by
    have pick (e : F) : ∃ x : V, pts x=e := by
      have edge := he e.val e.prop
      rw [show G=fromEdgeSet (↑(univ.image pts) : Set (Sym2 L)) from rfl,edgeSet_fromEdgeSet] at edge
      obtain ⟨x,_,eq⟩ := mem_image.mp edge.1
      exact ⟨x,eq⟩
    choose g sg using pick
    have inj : Function.Injective g := fun x y eq => Subtype.ext ((sg x).symm.trans ((congrArg pts eq).trans (sg y)))
    let I := univ.image g
    have ind : (colorGraph c k).IsIndepSet (I : Set V) := by
      intro x hx y hy xy edge
      obtain ⟨u,_,rfl⟩ := mem_image.mp hx
      obtain ⟨v,_,rfl⟩ := mem_image.mp hy
      have sep := hd u.prop v.prop (fun eq => xy (congrArg g (Subtype.ext eq)))
      rw [←sg u,←sg v] at sep
      have no := Finset.disjoint_left.mp sep
      rcases (repr _ _ xy).mp edge.2 with hp|hq
      · apply no (a:=Sum.inl (p (g u))) <;> simp [pts,Sym2.toFinset_mk_eq,hp]
      · apply no (a:=Sum.inr (q (g u))) <;> simp [pts,Sym2.toFinset_mk_eq,hq]
    have ub := ind.card_le_indepNum.trans (balanced_indepNum_le c hb k)
    simpa [I,card_image_of_injective _ inj] using ub
  obtain ⟨X,P,_,_,link,cost⟩ := matching_certificate G r matchCap
  let smallSide (B : Finset L) : Finset L := if B.toLeft.card≤B.toRight.card then
    B.toLeft.map Function.Embedding.inl else B.toRight.map Function.Embedding.inr
  have small (B : Finset L) : (smallSide B).card≤B.card/2 := by
    have eq := card_toLeft_add_card_toRight (u:=B)
    dsimp only [smallSide]
    split <;> rw [card_map] <;> omega
  let cover := X∪P.biUnion smallSide
  have coverSize : cover.card≤r := by
    have few := (card_biUnion_le : (P.biUnion smallSide).card≤∑ B∈P,(smallSide B).card).trans
      (sum_le_sum (fun B _ => small B))
    exact (card_union_le ..).trans ((Nat.add_le_add_left few _).trans cost)
  have every : (univ : Finset V)⊆cover.biUnion lines := by
    intro x _
    let l : L := Sum.inl (p x)
    let u : L := Sum.inr (q x)
    have ll : x∈lines l := by simp [lines,l,pts,Sym2.toFinset_mk_eq]
    have lu : x∈lines u := by simp [lines,u,pts,Sym2.toFinset_mk_eq]
    by_cases lx : l∈X
    · exact mem_biUnion.mpr ⟨l,mem_union_left _ lx,ll⟩
    by_cases ux : u∈X
    · exact mem_biUnion.mpr ⟨u,mem_union_left _ ux,lu⟩
    have ed : G.Adj l u := (fromEdgeSet_adj _).mpr ⟨mem_image.mpr ⟨x,mem_univ _,rfl⟩,by simp [l,u]⟩
    obtain ⟨B,hB,lb,ub⟩ := link l u lx ux ed
    by_cases h : B.toLeft.card≤B.toRight.card
    · apply mem_biUnion.mpr
      exact ⟨l,mem_union_right _ (mem_biUnion.mpr ⟨B,hB,by
        simp only [smallSide,h,ite_true]; exact mem_map.mpr ⟨p x,mem_toLeft.mpr lb,rfl⟩⟩),ll⟩
    · apply mem_biUnion.mpr
      exact ⟨u,mem_union_right _ (mem_biUnion.mpr ⟨B,hB,by
        simp only [smallSide,h,ite_false]; exact mem_map.mpr ⟨q x,mem_toRight.mpr ub,rfl⟩⟩),lu⟩
  have num := (card_le_card every).trans (card_biUnion_le_card_mul cover lines r (fun l _ => lineCap l))
  rw [card_univ] at num
  exact num.trans (by simpa [pow_two] using Nat.mul_le_mul_right r coverSize)

end Erdos617
