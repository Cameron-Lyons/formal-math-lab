import Erdos617.BlockSizes
import Erdos617.GreedyBlocks
import Erdos617.RankEdges

namespace Erdos617

open Finset SimpleGraph

private theorem pack_good_blocks {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℕ) (bs : List (TransversalBlock V))
    (hv : BlockTransversalValid G bs)
    (hgood : ∀ b ∈ bs, blockGap t b.vertices.card = 0 → b.cost = 0 → G.IsNClique t b.vertices) :
    ∃ P : Finset (Finset V), (P : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ A ∈ P, A ⊆ blockVertices bs ∧ G.IsNClique t A) ∧
      bs.length ≤ P.card + (bs.map (fun b => blockGap t b.vertices.card)).sum +
        (bs.map (·.cost)).sum := by
  classical
  induction bs with
  | nil => exact ⟨∅, by simp, by simp, by simp⟩
  | cons b bs ih =>
    obtain ⟨hd, hpiv, _, _, _, htail⟩ := hv
    obtain ⟨P, hdis, hall, hn⟩ := ih htail (fun c hc => hgood c (List.mem_cons_of_mem _ hc))
    have hdisj (A : Finset V) (hA : A ∈ P) : Disjoint b.vertices A :=
      hd.mono_right (hall A hA).1
    have hkeep (A : Finset V) (hA : A ∈ P) :
        A ⊆ blockVertices (b :: bs) ∧ G.IsNClique t A :=
      ⟨(hall A hA).1.trans subset_union_right, (hall A hA).2⟩
    by_cases h : G.IsNClique t b.vertices
    · have hfresh : b.vertices ∉ P := fun hP => disjoint_left.mp (hdisj _ hP) hpiv hpiv
      refine ⟨insert b.vertices P, ?_, ?_, ?_⟩
      · intro A ha B hb hab
        rcases mem_insert.mp ha with rfl | ha <;> rcases mem_insert.mp hb with rfl | hb
        · exact (hab rfl).elim
        · exact hdisj _ hb
        · exact (hdisj _ ha).symm
        · exact hdis ha hb hab
      · intro A ha
        rcases mem_insert.mp ha with rfl | ha
        · exact ⟨subset_union_left, h⟩
        · exact hkeep A ha
      · simp only [card_insert_of_notMem hfresh, List.length_cons, List.map_cons, List.sum_cons]
        omega
    · refine ⟨P, hdis, hkeep, ?_⟩
      have hbad := hgood b List.mem_cons_self
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      by_cases hg : blockGap t b.vertices.card = 0
      · have hc : b.cost ≠ 0 := fun hc => h (hbad hg hc)
        omega
      · omega

/-- A graph near the minimum edge count contains many disjoint full-sized
cliques when both its independence number and its clique number are bounded. -/
theorem many_clique_blocks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a t : ℕ} (ht : 2 ≤ t)
    (hN : Fintype.card V = t*a+1) (hα : G.IndepSetFree (a+1)) (hω : G.CliqueFree (t+1))
    (he : G.edgeFinset.card ≤ a*t.choose 2+t^2) :
    ∃ P : Finset (Finset V), (P : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ C ∈ P, G.IsNClique t C) ∧ a ≤ P.card+t^2 := by
  classical
  obtain ⟨bs, _, hv, hsize, hcost, hholes, _⟩ := exists_greedyBlocks G
  obtain ⟨I, _, hI⟩ := independent_pivots G bs hv
  have hlen : bs.length ≤ a := by
    by_contra! h
    obtain ⟨J, hJI, hJ⟩ := exists_subset_card_eq (s := I)
      (show a+1 ≤ I.card by rw [hI.card_eq]; omega)
    exact hα J ⟨hI.isIndepSet.mono hJI, hJ⟩
  let sizes := bs.map (fun b => b.vertices.card)
  have ha := total_block_gap_bound sizes a t (bs.map (fun b => b.cost)).sum ht
    (by simpa [sizes] using hlen) (by simpa [sizes, hN] using hsize)
    (by simpa [sizes, List.map_map, Function.comp_def, hcost] using he)
  simp only [sizes, List.map_map, Function.comp_def, List.length_map] at ha
  have hzero (b : TransversalBlock V) (hb : b ∈ bs) (hg : blockGap t b.vertices.card = 0)
      (hc : b.cost = 0) : G.IsNClique t b.vertices := by
    have hholes0 := hholes b hb
    rw [← card_inducedEdgeSet, hc] at hholes0
    have hcl : G.IsClique (b.vertices : Set V) := by
      intro x hx y hy hxy
      by_contra hnot
      have hedge : s(x,y) ∈ inducedEdgeSet Gᶜ b.vertices :=
        (mem_inducedEdgeSet _).mpr ⟨hx,hy,hxy,hnot⟩
      have := card_pos.mpr ⟨s(x,y), hedge⟩
      omega
    have hlow := (blockGap_spec t b.vertices.card).2
    have hhigh : b.vertices.card ≤ t := by
      by_contra! h
      obtain ⟨J, hJ, hcard⟩ := exists_subset_card_eq (s := b.vertices) h
      exact hω J ⟨hcl.subset hJ, hcard⟩
    exact ⟨hcl, by omega⟩
  obtain ⟨P, hd, hP, hc⟩ := pack_good_blocks G t bs hv hzero
  exact ⟨P, hd, fun C hC => (hP C hC).2, by omega⟩

end Erdos617
