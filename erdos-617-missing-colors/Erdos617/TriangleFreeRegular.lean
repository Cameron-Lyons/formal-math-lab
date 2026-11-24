import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace Erdos617

open Finset

/-- At this order, a triangle-free regular graph of degree `r-1` has an
independent set of at least `r` vertices. -/
theorem triangle_free_regular_impossible (r : ℕ) (hr : 6 ≤ r)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 2*r) (hdeg : ∀ v, G.degree v = r-1)
    (htri : G.CliqueFree 3) (hi : G.IndepSetFree r) : False := by
  classical
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  let A := G.neighborFinset v
  let B := (insert v A)ᶜ
  have memB {x : V} : x ∈ B ↔ x ≠ v ∧ ¬ G.Adj v x := by simp [B, A]
  have hA : A.card = r-1 := hdeg v
  have hB : B.card = r := by
    have := card_add_card_compl (insert v A)
    rw [card_insert_of_notMem (G.notMem_neighborFinset_self v), hA, hV] at this
    change (insert v A)ᶜ.card = r
    omega
  let D (b : V) := B.filter (G.Adj b)
  let M (a : V) := B.filter fun b => ¬ G.Adj a b
  have noTriangle {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
      False := htri {x,y,z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)
  have miss (a : V) (ha : a ∈ A) : (M a).card = 2 := by
    have hva := (G.mem_neighborFinset v a).mp ha
    have he : B.filter (G.Adj a) = (G.neighborFinset a).erase v := by
      ext b
      constructor
      · intro hb
        obtain ⟨hb, hab⟩ := mem_filter.mp hb
        exact mem_erase.mpr ⟨(memB.mp hb).1, (G.mem_neighborFinset a b).mpr hab⟩
      · intro hb
        obtain ⟨hbv, hba⟩ := mem_erase.mp hb
        have hab := (G.mem_neighborFinset a b).mp hba
        exact mem_filter.mpr ⟨memB.mpr ⟨hbv, fun hvb => noTriangle hva hvb hab⟩, hab⟩
    have hc := card_filter_add_card_filter_not (s := B) (G.Adj a)
    rw [he, card_erase_of_mem ((G.mem_neighborFinset a v).mpr hva.symm),
      G.card_neighborFinset_eq_degree, hdeg, hB] at hc
    change (B.filter fun b => ¬ G.Adj a b).card = 2
    omega
  have balance (b : V) (hb : b ∈ B) :
      (D b).card = (A.filter fun a => ¬ G.Adj a b).card := by
    let P := A.filter fun a => G.Adj a b
    have he : P ∪ D b = G.neighborFinset b := by
      ext w
      constructor
      · intro hw
        apply (G.mem_neighborFinset b w).mpr
        rcases mem_union.mp hw with hw | hw
        · exact (mem_filter.mp hw).2.symm
        · exact (mem_filter.mp hw).2
      · intro hw
        have hbw := (G.mem_neighborFinset b w).mp hw
        by_cases hwA : w ∈ A
        · exact mem_union_left _ (mem_filter.mpr ⟨hwA, hbw.symm⟩)
        · have hwB : w ∈ B := memB.mpr ⟨fun he => (memB.mp hb).2 (he ▸ hbw.symm),
              fun h => hwA ((G.mem_neighborFinset v w).mpr h)⟩
          exact mem_union_right _ (mem_filter.mpr ⟨hwB, hbw⟩)
    have hd : Disjoint P (D b) := by
      apply Finset.disjoint_left.mpr
      intro a ha h
      exact (memB.mp (mem_filter.mp h).1).2 ((G.mem_neighborFinset v a).mp (mem_filter.mp ha).1)
    have hcount := congrArg Finset.card he
    rw [card_union_of_disjoint hd, G.card_neighborFinset_eq_degree, hdeg] at hcount
    have hc := card_filter_add_card_filter_not (s := A) (fun a => G.Adj a b)
    change P.card + _ = _ at hc
    omega
  have small (b : V) (hb : b ∈ B) : (D b).card ≤ 2 := by
    by_contra! hbig
    have hn (a : V) (ha : a ∈ A) : ¬ G.Adj a b := by
      intro hab
      have hsub : D b ⊆ M a := by
        intro w hw
        obtain ⟨hwB, hbw⟩ := mem_filter.mp hw
        exact mem_filter.mpr ⟨hwB, fun haw => noTriangle hab haw hbw⟩
      have hle := card_le_card hsub
      rw [miss a ha] at hle
      omega
    have hcard := balance b hb
    rw [filter_eq_self.mpr hn, hA] at hcard
    have eq : D b = B.erase b := by
      apply eq_of_subset_of_card_le
      · intro w hw
        obtain ⟨hwB, hbw⟩ := mem_filter.mp hw
        exact mem_erase.mpr ⟨hbw.ne.symm, hwB⟩
      · rw [card_erase_of_mem hb, hB, hcard]
    have hind : G.IsIndepSet (B.erase b) := by
      rw [← eq]
      apply (G.isIndepSet_neighborSet_of_triangleFree htri b).mono
      intro x hx
      exact (mem_filter.mp hx).2
    have hlarge : G.IsIndepSet (insert v (B.erase b) : Finset V) := by
      rw [Finset.coe_insert]
      refine hind.insert (fun w hw _ => ?_)
      have hn := (memB.mp (mem_of_mem_erase hw)).2
      exact ⟨hn, fun h => hn h.symm⟩
    apply hi (insert v (B.erase b))
    refine ⟨hlarge, ?_⟩
    rw [card_insert_of_notMem (fun hv => (memB.mp (mem_of_mem_erase hv)).1 rfl),
      card_erase_of_mem hb, hB]
    omega
  have hsum : (∑ b ∈ B, (D b).card) = (r-1)*2 := by
    rw [sum_congr rfl balance, ← show (∑ a ∈ A, (M a).card) =
      ∑ b ∈ B, (A.filter fun a => ¬ G.Adj a b).card from
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun a b => ¬ G.Adj a b)]
    rw [sum_congr rfl miss]
    simp [hA]
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < A.card by omega)
  let Y := B.filter (G.Adj a)
  have split : Y ∪ M a = B := filter_union_filter_not_eq ..
  have part : Disjoint Y (M a) := disjoint_filter_filter_not ..
  have hY (y : V) (hy : y ∈ Y) : D y = (M a).filter (G.Adj y) := by
    ext z
    have hay := (mem_filter.mp hy).2
    constructor
    · intro hz
      obtain ⟨hzB, hyz⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hzB, fun haz => noTriangle hay haz hyz⟩, hyz⟩
    · intro hz
      obtain ⟨hzM, hyz⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨(mem_filter.mp hzM).1, hyz⟩
  have hYsum : (∑ y ∈ Y, (D y).card) ≤ (M a).card * 2 := by
    rw [sum_congr rfl (fun y hy => congrArg Finset.card (hY y hy))]
    rw [show (∑ y ∈ Y, ((M a).filter (G.Adj y)).card) =
      ∑ z ∈ M a, (Y.filter fun y => G.Adj y z).card from
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj]
    have bound (z : V) (hz : z ∈ M a) : (Y.filter fun y => G.Adj y z).card ≤ 2 := by
      apply le_trans _ (small z (mem_filter.mp hz).1)
      apply card_le_card
      intro y hy
      obtain ⟨hyY, hyz⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨(mem_filter.mp hyY).1, hyz.symm⟩
    simpa using sum_le_sum (s := M a) bound
  have hMsum : (∑ z ∈ M a, (D z).card) ≤ (M a).card * 2 := by
    simpa using sum_le_sum (s := M a) (fun z hz => small z (mem_filter.mp hz).1)
  rw [← split, sum_union part] at hsum
  rw [miss a ha] at hYsum hMsum
  omega

end Erdos617
