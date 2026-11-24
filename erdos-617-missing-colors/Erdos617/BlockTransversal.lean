import Erdos617.IndependentSets

namespace Erdos617

open SimpleGraph Finset

/-- One block of an ordered partition and the cost of edges to later blocks. -/
structure TransversalBlock (V : Type*) where
  vertices : Finset V
  pivot : V
  cost : ℕ

variable {V : Type*} [DecidableEq V]

/-- The union of the blocks in a list. -/
def blockVertices : List (TransversalBlock V) → Finset V
  | [] => ∅
  | b :: bs => b.vertices ∪ blockVertices bs

/-- Earlier pivots have no later neighbors. Each other choice in a block
forbids at most the stated number of vertices in later blocks. -/
def BlockTransversalValid (G : SimpleGraph V) [DecidableRel G.Adj] :
    List (TransversalBlock V) → Prop
  | [] => True
  | b :: bs =>
      Disjoint b.vertices (blockVertices bs) ∧ b.pivot ∈ b.vertices ∧
      (∀ z ∈ blockVertices bs, ¬ G.Adj b.pivot z) ∧
      (∀ x ∈ b.vertices, ((blockVertices bs).filter (G.Adj x)).card ≤ b.cost) ∧
      (∀ x ∈ b.vertices, ∀ y ∈ b.vertices, x ≠ y → ¬ G.Adj x y →
        ((blockVertices bs).filter (G.Adj x)).card +
          ((blockVertices bs).filter (G.Adj y)).card ≤ b.cost + 1) ∧
      BlockTransversalValid G bs

/-- The pivots of a valid list form an independent set. -/
theorem independent_pivots (G : SimpleGraph V) [DecidableRel G.Adj]
    (bs : List (TransversalBlock V)) (hv : BlockTransversalValid G bs) :
    ∃ I ⊆ blockVertices bs, G.IsNIndepSet bs.length I := by
  induction bs with
  | nil => exact ⟨∅, by simp, by simp [SimpleGraph.IsIndepSet], rfl⟩
  | cons b bs ih =>
    obtain ⟨hd, hpiv, hpout, _, _, htail⟩ := hv
    obtain ⟨I, hI, hind⟩ := ih htail
    have hpI : b.pivot ∉ I := fun h ↦ Finset.disjoint_left.mp hd hpiv (hI h)
    exact ⟨insert b.pivot I, insert_subset (mem_union_left _ hpiv)
      (fun z hz ↦ mem_union_right _ (hI hz)), independent_insert_of_nonadjacent G
        hind.isIndepSet b.pivot (fun z hz ↦ hpout z (hI hz)),
      by simp [card_insert_of_notMem hpI, hind.card_eq]⟩

private theorem choose_avoiding_blocks (G : SimpleGraph V) [DecidableRel G.Adj]
    (bs : List (TransversalBlock V)) (hv : BlockTransversalValid G bs) (F : Finset V)
    (hw : ∀ b ∈ bs, F.card + (bs.map TransversalBlock.cost).sum < b.vertices.card) :
    ∃ I ⊆ blockVertices bs, Disjoint I F ∧ G.IsNIndepSet bs.length I := by
  induction bs generalizing F with
  | nil => exact ⟨∅, by simp, by simp, by simp [SimpleGraph.IsIndepSet], rfl⟩
  | cons b bs ih =>
    obtain ⟨hd, _, _, hout, _, htail⟩ := hv
    have hbound := hw b List.mem_cons_self
    simp only [List.map_cons, List.sum_cons] at hbound
    obtain ⟨x, hx, hxf⟩ : ∃ x ∈ b.vertices, x ∉ F := by
      by_contra! hall
      have := card_le_card (show b.vertices ⊆ F from fun x h ↦ hall x h)
      omega
    let N := (blockVertices bs).filter (G.Adj x)
    have hcard := (card_union_le F N).trans (Nat.add_le_add_left (hout x hx) F.card)
    have hrest (c : TransversalBlock V) (hc : c ∈ bs) :
        (F ∪ N).card + (bs.map TransversalBlock.cost).sum < c.vertices.card := by
      have h := hw c (List.mem_cons_of_mem _ hc)
      simp only [List.map_cons, List.sum_cons] at h
      omega
    obtain ⟨I, hI, havoid, hind⟩ := ih htail (F ∪ N) hrest
    have hxI : x ∉ I := fun h ↦ Finset.disjoint_left.mp hd hx (hI h)
    refine ⟨insert x I, insert_subset (mem_union_left _ hx)
      (fun z hz ↦ mem_union_right _ (hI hz)), ?_, ?_, ?_⟩
    · exact Finset.disjoint_insert_left.mpr ⟨hxf, havoid.mono_right subset_union_left⟩
    · apply independent_insert_of_nonadjacent G hind.isIndepSet
      intro z hz h
      exact Finset.disjoint_left.mp havoid hz
        (mem_union_right _ (mem_filter.mpr ⟨hI hz, h⟩))
    · simp [card_insert_of_notMem hxI, hind.card_eq]

/-- If a block contains a nonadjacent pair, take both of its vertices,
earlier pivots, and one unblocked vertex from each later block. -/
theorem larger_independent_of_nonclique_block (G : SimpleGraph V) [DecidableRel G.Adj]
    (bs : List (TransversalBlock V)) (hv : BlockTransversalValid G bs)
    (hw : ∀ b ∈ bs, (bs.map TransversalBlock.cost).sum + 1 < b.vertices.card)
    (hbad : ∃ b ∈ bs, ¬ G.IsClique (b.vertices : Set V)) :
    ∃ I ⊆ blockVertices bs, G.IsNIndepSet (bs.length + 1) I := by
  induction bs with
  | nil => simp at hbad
  | cons b bs ih =>
    obtain ⟨hd, hpiv, hpout, _, htwo, htail⟩ := hv
    by_cases hcl : G.IsClique (b.vertices : Set V)
    · obtain ⟨bad, hmem, hnb⟩ := hbad
      have hmem' : bad ∈ bs := (List.mem_cons.mp hmem).resolve_left (fun h ↦ hnb (h ▸ hcl))
      have hrest (c : TransversalBlock V) (hc : c ∈ bs) :
          (bs.map TransversalBlock.cost).sum + 1 < c.vertices.card := by
        have h := hw c (List.mem_cons_of_mem _ hc)
        simp only [List.map_cons, List.sum_cons] at h
        omega
      obtain ⟨I, hI, hind⟩ := ih htail hrest ⟨bad, hmem', hnb⟩
      have hpI : b.pivot ∉ I := fun h ↦ Finset.disjoint_left.mp hd hpiv (hI h)
      refine ⟨insert b.pivot I, insert_subset (mem_union_left _ hpiv)
        (fun z hz ↦ mem_union_right _ (hI hz)), ?_, ?_⟩
      · exact independent_insert_of_nonadjacent G hind.isIndepSet b.pivot
          fun z hz ↦ hpout z (hI hz)
      · simp [card_insert_of_notMem hpI, hind.card_eq]
    · obtain ⟨x, hx, y, hy, hne, hxy⟩ :
          ∃ x ∈ b.vertices, ∃ y ∈ b.vertices, x ≠ y ∧ ¬ G.Adj x y := by
        by_contra! h
        exact hcl fun x hx y hy hne ↦ h x hx y hy hne
      let X := (blockVertices bs).filter (G.Adj x)
      let Y := (blockVertices bs).filter (G.Adj y)
      have hcard := (card_union_le X Y).trans (htwo x hx y hy hne hxy)
      have hrest (c : TransversalBlock V) (hc : c ∈ bs) :
          (X ∪ Y).card + (bs.map TransversalBlock.cost).sum < c.vertices.card := by
        have h := hw c (List.mem_cons_of_mem _ hc)
        simp only [List.map_cons, List.sum_cons] at h
        omega
      obtain ⟨I, hI, havoid, hind⟩ := choose_avoiding_blocks G bs htail (X ∪ Y) hrest
      have hxI : x ∉ I := fun h ↦ Finset.disjoint_left.mp hd hx (hI h)
      have hyI : y ∉ insert x I := by
        exact fun h ↦ (mem_insert.mp h).elim hne.symm
          (fun h ↦ Finset.disjoint_left.mp hd hy (hI h))
      have hxind := independent_insert_of_nonadjacent G hind.isIndepSet x (by
        intro z hz hadj
        exact Finset.disjoint_left.mp havoid hz
          (mem_union_left _ (mem_filter.mpr ⟨hI hz, hadj⟩)))
      refine ⟨insert y (insert x I), insert_subset (mem_union_left _ hy)
        (insert_subset (mem_union_left _ hx) (fun z hz ↦ mem_union_right _ (hI hz))), ?_, ?_⟩
      · apply independent_insert_of_nonadjacent G hxind
        intro z hz hadj
        rcases mem_insert.mp hz with rfl | hz
        · exact hxy hadj.symm
        · exact Finset.disjoint_left.mp havoid hz
            (mem_union_right _ (mem_filter.mpr ⟨hI hz, hadj⟩))
      · simp [card_insert_of_notMem hyI, card_insert_of_notMem hxI, hind.card_eq]

end Erdos617
