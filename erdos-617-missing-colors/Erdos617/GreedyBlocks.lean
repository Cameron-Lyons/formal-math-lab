import Erdos617.BlockTransversal
import Erdos617.BlockAccount

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each pivot has minimum degree in the remaining vertices, and its
closed neighborhood there is precisely its own block. -/
def GreedyBlockPivots : List (TransversalBlock V) → Prop
  | [] => True
  | b :: bs =>
    let R := b.vertices ∪ blockVertices bs
    b.vertices = insert b.pivot (R.filter (G.Adj b.pivot)) ∧
      (∀ x ∈ R, (R.filter (G.Adj b.pivot)).card ≤ (R.filter (G.Adj x)).card) ∧
      GreedyBlockPivots bs

/-- Greedy elimination restricted to a finite set of vertices. -/
theorem exists_greedyBlocks_on (R : Finset V) :
    ∃ bs : List (TransversalBlock V), blockVertices bs = R ∧
      BlockTransversalValid G bs ∧
      (bs.map (fun b => b.vertices.card)).sum = R.card ∧
      (bs.map (fun b => b.vertices.card.choose 2)).sum + (bs.map (·.cost)).sum = blockEdges G R ∧
      (∀ b ∈ bs, blockEdges Gᶜ b.vertices ≤ b.cost) ∧ GreedyBlockPivots G bs := by
  classical
  induction R using Finset.strongInductionOn with
  | _ R ih =>
    by_cases hR : R.Nonempty
    · obtain ⟨p, hp, hmin⟩ := R.exists_min_image (fun v => (R.filter (G.Adj v)).card) hR
      let B := insert p (R.filter (G.Adj p))
      let T := R \ B
      have hBp : p ∈ B := mem_insert_self ..
      have hBR : B ⊆ R := insert_subset hp (filter_subset ..)
      have hd : Disjoint B T := disjoint_sdiff
      have hu : B ∪ T = R := union_sdiff_of_subset hBR
      have hcard : B.card = (R.filter (G.Adj p)).card + 1 := by simp [B]
      have hbound (x : V) (hx : x ∈ B) :
          B.card ≤ ((B ∪ T).filter (G.Adj x)).card + 1 := by
        rw [hu, hcard]
        exact Nat.add_le_add_right (hmin x (hBR hx)) 1
      obtain ⟨cost, hcount, hholes, h1, h2⟩ := block_account G B T hd hbound
      obtain ⟨bs, hcover, hvalid, hsize, hedges, htHoles, hpiv⟩ :=
        ih T (sdiff_ssubset hBR ⟨p, hBp⟩)
      let b : TransversalBlock V := ⟨B, p, cost⟩
      refine ⟨b :: bs, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change B ∪ blockVertices bs = R
        rwa [hcover]
      · change Disjoint B (blockVertices bs) ∧ p ∈ B ∧ _ ∧ _ ∧ _ ∧ _
        rw [hcover]
        refine ⟨hd, hBp, ?_, h1, h2, hvalid⟩
        intro z hz haz
        exact (mem_sdiff.mp hz).2 (mem_insert_of_mem (mem_filter.mpr ⟨(mem_sdiff.mp hz).1,haz⟩))
      · simp only [List.map_cons, List.sum_cons, b]
        rw [hsize, ← card_union_of_disjoint hd, hu]
      · simp only [List.map_cons, List.sum_cons, b]
        rw [hu] at hcount
        omega
      · intro b' hb'
        rcases List.mem_cons.mp hb' with rfl | h
        · exact hholes
        · exact htHoles b' h
      · change B = insert p ((B ∪ blockVertices bs).filter (G.Adj p)) ∧ _ ∧ _
        simp only [b, hcover, hu]
        exact ⟨rfl, hmin, hpiv⟩
    · rw [not_nonempty_iff_eq_empty.mp hR]
      have zero : blockEdges G ∅ = 0 := by
        have h := (G.induce (↑(∅ : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
        change blockEdges G ∅ ≤ (Fintype.card (∅ : Finset V)).choose 2 at h
        simpa using h
      exact ⟨[], rfl, trivial, rfl, zero.symm, by simp, trivial⟩

/-- Successively taking the closed neighborhood of a minimum-degree vertex
partitions the graph and accounts for all of its edges. -/
theorem exists_greedyBlocks [Fintype V] :
    ∃ bs : List (TransversalBlock V), blockVertices bs = univ ∧
      BlockTransversalValid G bs ∧
      (bs.map (fun b => b.vertices.card)).sum = Fintype.card V ∧
      (bs.map (fun b => b.vertices.card.choose 2)).sum + (bs.map (·.cost)).sum =
        G.edgeFinset.card ∧
      (∀ b ∈ bs, blockEdges Gᶜ b.vertices ≤ b.cost) ∧ GreedyBlockPivots G bs := by
  simpa only [Finset.card_univ, blockEdges_univ] using exists_greedyBlocks_on G univ

end Erdos617
