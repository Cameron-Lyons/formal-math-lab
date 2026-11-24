import Erdos617.ColorGraph
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos617

open Finset SimpleGraph

/-- When each exception misses at most M vertices of at least one monochromatic
clique, some enlarged clique must account for all other colors using those
missing edges and edges between exceptions. -/
theorem cluster_capacity {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]
    {r t D M : ℕ} (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (S X : Finset V) (B : ι → Finset V) (ht : Fintype.card ι = t)
    (hS : S.card = t*r+1) (hc : ∀ a, (colorGraph c k).IsClique (B a : Set V))
    (hcover : S ⊆ (univ.biUnion B) ∪ X) (hX : X.card ≤ D)
    (hnear : ∀ x ∈ X, ∃ a, ((B a).filter fun y => ¬ (colorGraph c k).Adj x y).card ≤ M) :
    r-1 ≤ D*M+D^2 := by
  classical
  let miss (x : V) (a : ι) := (B a).filter fun y => ¬ (colorGraph c k).Adj x y
  let Y (a : ι) := X.filter fun x => (miss x a).card ≤ M
  let enlarge (a : ι) := B a ∪ Y a
  have cover : S ⊆ univ.biUnion enlarge := by
    intro x hx
    rcases mem_union.mp (hcover hx) with hx | hx
    · obtain ⟨a, ha, h⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨a, ha, mem_union_left _ h⟩
    · obtain ⟨a, ha⟩ := hnear x hx
      exact mem_biUnion.mpr ⟨a, mem_univ _, mem_union_right _ (mem_filter.mpr ⟨hx, ha⟩)⟩
  obtain ⟨a, hlarge⟩ : ∃ a, r < (enlarge a).card := by
    by_contra! hsmall
    have h := (card_le_card cover).trans
      (card_biUnion_le_card_mul univ enlarge r (fun a _ => hsmall a))
    rw [hS, card_univ, ht] at h
    omega
  obtain ⟨T, hT, hsize⟩ := exists_subset_card_eq (Nat.succ_le_of_lt hlarge)
  let colors (x : V) := ((miss x a) ∪ Y a).image fun y => c s(x,y)
  have hcols : univ.erase k ⊆ (Y a).biUnion colors := by
    intro j hj
    have hjk := (mem_erase.mp hj).1
    obtain ⟨u, hu, v, hv, huv, he⟩ := hb T hsize j
    have spoke (x y : V) (hx : x ∈ Y a) (hy : y ∈ enlarge a) (hxy : c s(x,y) = j) :
        j ∈ (Y a).biUnion colors := by
      refine mem_biUnion.mpr ⟨x, hx, mem_image.mpr ⟨y, ?_, hxy⟩⟩
      rcases mem_union.mp hy with hyB | hyY
      · exact mem_union_left _ (mem_filter.mpr ⟨hyB, fun e => hjk (hxy.symm.trans e.2)⟩)
      · exact mem_union_right _ hyY
    rcases mem_union.mp (hT hu) with huB | huY
    · rcases mem_union.mp (hT hv) with hvB | hvY
      · exact (hjk (he.symm.trans ((hc a) huB hvB huv).2)).elim
      · exact spoke v u hvY (hT hu) (by rwa [Sym2.eq_swap])
    · exact spoke u v huY (hT hv) he
  have hy : (Y a).card ≤ D := (card_le_card (filter_subset ..)).trans hX
  have per (x : V) (hx : x ∈ Y a) : (colors x).card ≤ M+D := by
    refine card_image_le.trans ((card_union_le _ _).trans ?_)
    exact Nat.add_le_add (mem_filter.mp hx).2 hy
  have hcount := (card_le_card hcols).trans (card_biUnion_le_card_mul _ _ _ per)
  rw [card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin] at hcount
  simpa [Nat.mul_add, pow_two] using hcount.trans (Nat.mul_le_mul_right (M+D) hy)

end Erdos617
