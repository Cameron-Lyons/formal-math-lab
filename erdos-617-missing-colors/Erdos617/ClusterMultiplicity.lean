module

public import Erdos617.ColorGraph
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Erdos617

open SimpleGraph Finset

theorem enlarged_clique_budget {V : Type*} [DecidableEq V] {r : ℕ}
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (B Y : Finset V)
    (hc : (colorGraph c k).IsClique (B : Set V)) (hd : Disjoint B Y) :
    (r-1)*(B.card+Y.card) ≤ (r-1)*r +
      (∑ x ∈ Y, (B.filter fun y => ¬(colorGraph c k).Adj x y).card) + Y.card^2 := by
  classical
  let miss (x : V) := B.filter fun y => ¬ (colorGraph c k).Adj x y
  let colors (x : V) := ((miss x) ∪ Y).image fun y => c s(x,y)
  let hit (j : Fin r) := Y.filter fun x => j ∈ colors x
  let F := univ.erase k
  have cover (j : Fin r) (hj : j ∈ F) : B.card+Y.card ≤ r+(hit j).card := by
    have hjk := (mem_erase.mp hj).1
    have hs : hit j ⊆ B ∪ Y := (filter_subset ..).trans subset_union_right
    have hc' : ((B ∪ Y) \ hit j).card ≤ r := by
      by_contra! hlarge
      obtain ⟨T,hT,hn⟩ := exists_subset_card_eq (Nat.succ_le_of_lt hlarge)
      obtain ⟨u,hu,v,hv,huv,he⟩ := hb T hn j
      obtain ⟨huBY,huH⟩ := mem_sdiff.mp (hT hu)
      obtain ⟨hvBY,hvH⟩ := mem_sdiff.mp (hT hv)
      have spoke (x y : V) (hx : x ∈ Y) (hy : y ∈ B ∪ Y) (hxy : c s(x,y)=j) :
          x ∈ hit j := by
        refine mem_filter.mpr ⟨hx, mem_image.mpr ⟨y, ?_, hxy⟩⟩
        rcases mem_union.mp hy with hy | hy
        · exact mem_union_left _ (mem_filter.mpr ⟨hy, fun e => hjk (hxy.symm.trans e.2)⟩)
        · exact mem_union_right _ hy
      rcases mem_union.mp huBY with huB | huY
      · rcases mem_union.mp hvBY with hvB | hvY
        · exact hjk (he.symm.trans (hc huB hvB huv).2)
        · exact hvH (spoke v u hvY huBY (by rwa [Sym2.eq_swap]))
      · exact huH (spoke u v huY hvBY he)
    have hn := card_sdiff_add_card_eq_card hs
    rw [card_union_of_disjoint hd] at hn
    omega
  have hsum := sum_le_sum (s := F) cover
  have hcnt : (∑ j ∈ F, (hit j).card) =
      ∑ x ∈ Y, (F.filter fun j => j ∈ colors x).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun j x => j ∈ colors x)
  have hstep (x : V) (_ : x ∈ Y) :
      (F.filter fun j => j ∈ colors x).card ≤ (miss x).card+Y.card := by
    have subset : (F.filter fun j => j ∈ colors x) ⊆ colors x := fun _ h => (mem_filter.mp h).2
    exact (card_le_card subset).trans (card_image_le.trans (card_union_le ..))
  have hi := sum_le_sum (s := Y) hstep
  have hf : F.card = r-1 := by simp [F]
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, hf, Nat.cast_id] at hsum hi
  rw [hcnt] at hsum
  change (r-1)*(B.card+Y.card) ≤ _+(∑ x ∈ Y,(miss x).card)+Y.card^2
  rw [pow_two, Nat.mul_add]
  omega

/-- Assigning exceptions to several cliques gives an additional r−1 required
foreign-color incidences for each membership beyond the first. -/
theorem cluster_multiplicity_capacity {V ι : Type*} [DecidableEq V] [Fintype ι] {r t D H : ℕ}
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r)
    (B : ι → Finset V) (X : Finset V) (Y : ι → Finset V) (ht : Fintype.card ι = t)
    (hc : ∀ i, (colorGraph c k).IsClique (B i : Set V)) (hdis : ∀ i, Disjoint (B i) (Y i))
    (hcover : t*r+1 ≤ (∑ i, (B i).card)+X.card) (hY : ∀ i, Y i ⊆ X) (hX : X.card ≤ D)
    (hlower : X.card+H ≤ ∑ i, (Y i).card) (hupper : (∑ i, (Y i).card) ≤ 2*D) :
    (r-1)*(1+H) ≤ (∑ i, ∑ x ∈ Y i,
        ((B i).filter fun y => ¬(colorGraph c k).Adj x y).card)+2*D^2 := by
  have per := sum_le_sum (s := univ) fun i _ =>
    enlarged_clique_budget c hb k (B i) (Y i) (hc i) (hdis i)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, ht, nsmul_eq_mul,
    Nat.cast_id] at per
  have pairs : (∑ i, (Y i).card^2) ≤ 2*D^2 := by
    have each (i : ι) (_ : i ∈ univ) : (Y i).card^2 ≤ D*(Y i).card := by
      rw [pow_two]
      exact Nat.mul_le_mul_right _ ((card_le_card (hY i)).trans hX)
    have hp := sum_le_sum (s := univ) each
    rw [← mul_sum] at hp
    nlinarith only [hp,Nat.mul_le_mul_left D hupper]
  have demand := Nat.mul_le_mul_left (r-1)
    (show t*r+1+H ≤ (∑ i, (B i).card)+(∑ i, (Y i).card) by omega)
  nlinarith only [per, pairs, demand]

end Erdos617
