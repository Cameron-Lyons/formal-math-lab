module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Number of graph edges induced by a finite vertex set. -/
def blockEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.induce (S : Set V)).edgeFinset.card

omit [DecidableEq V] in
theorem block_degree_sum (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∑ x ∈ S, (S.filter (G.Adj x)).card = 2 * blockEdges G S := by
  let H := G.induce (S : Set V)
  have count (x : S) : H.degree x = (S.filter (G.Adj x.val)).card := by
    have he : (H.neighborFinset x).map (Function.Embedding.subtype (· ∈ S)) =
        S.filter (G.Adj x.val) := by
      ext v
      constructor
      · intro hv
        obtain ⟨y, hy, rfl⟩ := mem_map.mp hv
        exact mem_filter.mpr ⟨y.prop, (H.mem_neighborFinset x y).mp hy⟩
      · intro hv
        obtain ⟨hvS, hadj⟩ := mem_filter.mp hv
        exact mem_map.mpr ⟨⟨v, hvS⟩, (H.mem_neighborFinset _ _).mpr hadj, rfl⟩
    simpa only [card_map, card_neighborFinset_eq_degree] using congrArg Finset.card he
  calc
    _ = ∑ x : S, (S.filter (G.Adj x.val)).card :=
      sum_subtype S (fun _ => Iff.rfl) _
    _ = ∑ x : S, H.degree x := sum_congr rfl fun x _ => (count x).symm
    _ = _ := H.sum_degrees_eq_twice_card_edges

omit [DecidableEq V] in
theorem blockEdges_univ [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    blockEdges G univ = G.edgeFinset.card := by
  have hs := block_degree_sum G (univ : Finset V)
  have hd (x : V) : (univ.filter (G.Adj x)).card = G.degree x := by
    rw [← G.card_neighborFinset_eq_degree x]
    congr 1
    ext z
    simp [mem_neighborFinset]
  simp_rw [hd] at hs
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  omega

private theorem filter_union_card {B T : Finset V} (hd : Disjoint B T)
    (p : V → Prop) [DecidablePred p] :
    ((B ∪ T).filter p).card = (B.filter p).card + (T.filter p).card := by
  rw [filter_union, card_union_of_disjoint (hd.mono (filter_subset ..) (filter_subset ..))]

theorem blockEdges_union (G : SimpleGraph V) [DecidableRel G.Adj]
    {A T : Finset V} (hd : Disjoint A T) :
    blockEdges G (A ∪ T) = blockEdges G A + (∑ x ∈ A, (T.filter (G.Adj x)).card) +
      blockEdges G T := by
  have hs := block_degree_sum G (A ∪ T)
  simp_rw [filter_union_card hd] at hs
  rw [sum_union hd, sum_add_distrib, sum_add_distrib, block_degree_sum, block_degree_sum] at hs
  have hcross : (∑ z ∈ T, (A.filter (G.Adj z)).card) = ∑ x ∈ A, (T.filter (G.Adj x)).card := by
    calc
      _ = ∑ x ∈ A, (T.filter fun z => G.Adj z x).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
      _ = _ := sum_congr rfl fun x _ => congrArg Finset.card (filter_congr fun z _ => G.adj_comm z x)
  omega

private theorem degree_sum_on_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hAB : A ⊆ B) :
    ∑ x ∈ A, (B.filter (G.Adj x)).card ≤ blockEdges G B + blockEdges G A := by
  let T := B \ A
  have hd : Disjoint A T := Finset.disjoint_left.mpr fun _ hx ht => (Finset.mem_sdiff.mp ht).2 hx
  have he : A ∪ T = B := union_sdiff_of_subset hAB
  have hs := blockEdges_union G hd
  rw [← he]
  simp_rw [filter_union_card hd, sum_add_distrib, block_degree_sum]
  omega

private theorem blockEdges_add_compl (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    blockEdges G B + blockEdges Gᶜ B = B.card.choose 2 := by
  let H := G.induce (B : Set V)
  let K := Gᶜ.induce (B : Set V)
  have hcompl (x y : B) : K.Adj x y ↔ x ≠ y ∧ ¬ H.Adj x y :=
    and_congr (not_congr Subtype.val_inj) Iff.rfl
  have he : H.edgeFinset ∪ K.edgeFinset = (⊤ : SimpleGraph B).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      by_cases h : H.Adj x y
      · simp [mem_edgeFinset, hcompl, h, h.ne]
      · simp [mem_edgeFinset, hcompl, h]
  have hd : Disjoint H.edgeFinset K.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | _ x y => exact fun hx hy => ((hcompl x y).mp (mem_edgeFinset.mp hy)).2 (mem_edgeFinset.mp hx)
  change H.edgeFinset.card + K.edgeFinset.card = _
  rw [← card_union_of_disjoint hd, he, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_coe]

/-- Closed-neighborhood elimination at minimum degree. The cost is the number of
missing pairs in the block plus the sum of its degrees above the pivot's degree. -/
theorem block_account_with_subsets (G : SimpleGraph V) [DecidableRel G.Adj] (B T : Finset V)
    (hdis : Disjoint B T) (hmin : ∀ x ∈ B, B.card ≤ ((B ∪ T).filter (G.Adj x)).card + 1) :
    ∃ cost : ℕ, blockEdges G (B ∪ T) = B.card.choose 2 + cost + blockEdges G T ∧
      blockEdges Gᶜ B ≤ cost ∧
      (∀ x ∈ B, (T.filter (G.Adj x)).card ≤ cost) ∧
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → ¬G.Adj x y →
        (T.filter (G.Adj x)).card + (T.filter (G.Adj y)).card ≤ cost+1) ∧
      ∀ A ⊆ B, (∑ x ∈ A, (T.filter (G.Adj x)).card) ≤ cost+A.card.choose 2 := by
  classical
  let out (x : V) := (T.filter (G.Adj x)).card
  let holes (x : V) := (B.filter (Gᶜ.Adj x)).card
  let extra (x : V) := out x - holes x
  have split (x : V) (hx : x ∈ B) : holes x + extra x = out x := by
    have hd := hmin x hx
    rw [filter_union_card hdis] at hd
    have parts : B.filter (G.Adj x) ∪ B.filter (Gᶜ.Adj x) = B.erase x := by
      ext y
      by_cases h : G.Adj x y
      · simp [h, h.ne, h.ne.symm]
      · simp [h, ne_comm, and_comm]
    have dis : Disjoint (B.filter (G.Adj x)) (B.filter (Gᶜ.Adj x)) :=
      disjoint_left.mpr fun _ h j => (mem_filter.mp j).2.2 (mem_filter.mp h).2
    have hc := congrArg Finset.card parts
    rw [card_union_of_disjoint dis, card_erase_of_mem hx] at hc
    have hn := card_pos.mpr ⟨x, hx⟩
    dsimp [holes, extra, out]
    omega
  let E := ∑ x ∈ B, extra x
  let H := blockEdges Gᶜ B
  have bound {A : Finset V} (hAB : A ⊆ B) :
      (∑ x ∈ A, out x) ≤ H + E + blockEdges Gᶜ A := by
    calc
      _ = ∑ x ∈ A, (holes x + extra x) := sum_congr rfl fun x hx => (split x (hAB hx)).symm
      _ = (∑ x ∈ A, holes x) + (∑ x ∈ A, extra x) := sum_add_distrib
      _ ≤ (H + blockEdges Gᶜ A) + E :=
        Nat.add_le_add (degree_sum_on_subset Gᶜ hAB) (sum_le_sum_of_subset hAB)
      _ = _ := by omega
  have hsum : (∑ x ∈ B, out x) = 2*H + E := calc
    _ = ∑ x ∈ B, (holes x + extra x) := sum_congr rfl fun x hx => (split x hx).symm
    _ = _ := by rw [sum_add_distrib, show (∑ x ∈ B, holes x) = 2*H from block_degree_sum Gᶜ B]
  have cap (A : Finset V) : blockEdges Gᶜ A ≤ A.card.choose 2 := by
    simpa [blockEdges] using (Gᶜ.induce (A : Set V)).card_edgeFinset_le_card_choose_two
  refine ⟨H+E, ?_, Nat.le_add_right _ _, ?_, ?_, fun A ha => (bound ha).trans (Nat.add_le_add_left (cap A) _)⟩
  · have hc := blockEdges_add_compl G B
    rw [blockEdges_union G hdis]
    change blockEdges G B + (∑ x ∈ B, out x) + blockEdges G T = _
    change blockEdges G B + H = _ at hc
    omega
  · intro x hx
    have he := bound (singleton_subset_iff.mpr hx)
    have hc := cap {x}
    simp at hc he
    change out x ≤ _
    omega
  · intro x hx y hy hxy _
    have he := bound (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
    have hc := cap {x,y}
    simp [hxy] at he hc
    change out x + out y ≤ _
    omega

/-- The single- and two-vertex closed-neighborhood cost bounds. -/
theorem block_account (G : SimpleGraph V) [DecidableRel G.Adj] (B T : Finset V)
    (hdis : Disjoint B T) (hmin : ∀ x ∈ B, B.card ≤ ((B ∪ T).filter (G.Adj x)).card + 1) :
    ∃ cost : ℕ, blockEdges G (B ∪ T) = B.card.choose 2 + cost + blockEdges G T ∧
      blockEdges Gᶜ B ≤ cost ∧
      (∀ x ∈ B, (T.filter (G.Adj x)).card ≤ cost) ∧
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → ¬G.Adj x y →
        (T.filter (G.Adj x)).card + (T.filter (G.Adj y)).card ≤ cost+1) := by
  obtain ⟨d,eq,holes,one,two,_⟩ := block_account_with_subsets G B T hdis hmin
  exact ⟨d,eq,holes,one,two⟩

end Erdos617
