import Erdos617.ClusterProximity

namespace Erdos617

open Finset SimpleGraph

/-- Vertices in S with at most q nonneighbors in block i and more than q
nonneighbors in each other block. -/
noncomputable def singleBlock {V ι : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : ι → Finset V) (q : ℕ) (S : Finset V) (i : ι) : Finset V := by
  classical
  exact S.filter fun x => ((B i).filter fun z => ¬ G.Adj x z).card ≤ q ∧
    ∀ j, j ≠ i → q < ((B j).filter fun z => ¬ G.Adj x z).card

theorem mem_singleBlock {V ι : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : ι → Finset V} {q : ℕ} {S : Finset V} {i : ι} {x : V} :
    x ∈ singleBlock G B q S i ↔ x ∈ S ∧
      ((B i).filter fun z => ¬ G.Adj x z).card ≤ q ∧
      ∀ j, j ≠ i → q < ((B j).filter fun z => ¬ G.Adj x z).card := by
  classical
  simp only [singleBlock, mem_filter]

/-- Two vertices uniquely close to one block must be adjacent. Otherwise
the remaining blocks have a transversal of common nonneighbors, giving a
forbidden independent set together with these two vertices. -/
theorem MinimalObstruction.singleBlock_isClique {V ι : Type*} [DecidableEq V] [Fintype ι]
    {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}
    (h : MinimalObstruction c k t S) (B : ι → Finset V) (ht : Fintype.card ι = t)
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (hBS : ∀ i, B i ⊆ S)
    (hsize : ∀ i, (B i).card ≤ r) (F : Finset (Sym2 V))
    (hcross : ∀ i j, i ≠ j → ∀ u ∈ B i, ∀ v ∈ B j, (colorGraph c k).Adj u v → s(u,v) ∈ F)
    {q : ℕ} (hscale : r + Nat.sqrt F.card + 3 ≤ 2*q) (i : ι) :
    (colorGraph c k).IsClique (singleBlock (colorGraph c k) B q S i : Set V) := by
  classical
  let G := colorGraph c k
  intro x hx y hy hxy
  by_contra hnot
  obtain ⟨hxS, _, hxfar⟩ := (mem_singleBlock G).mp hx
  obtain ⟨hyS, _, hyfar⟩ := (mem_singleBlock G).mp hy
  let K := (univ : Finset ι).erase i
  let N (v : V) (j : K) := (B j.val).filter fun z => ¬ G.Adj v z
  let Y (j : K) := (((N x j ∩ N y j).erase x).erase y)
  have hYsub (j : K) : Y j ⊆ B j.val :=
    (erase_subset ..).trans ((erase_subset ..).trans (inter_subset_left.trans (filter_subset ..)))
  have hYcard (j : K) : Nat.sqrt F.card+1 ≤ (Y j).card := by
    have hxj : q < (N x j).card := hxfar j (mem_erase.mp j.prop).1
    have hyj : q < (N y j).card := hyfar j (mem_erase.mp j.prop).1
    have hu : (N x j ∪ N y j).card ≤ r :=
      (card_le_card (union_subset (filter_subset ..) (filter_subset ..))).trans (hsize j)
    have hc := card_union_add_card_inter (N x j) (N y j)
    have hex := (N x j ∩ N y j).pred_card_le_card_erase (a := x)
    have hey := ((N x j ∩ N y j).erase x).pred_card_le_card_erase (a := y)
    dsimp [Y]
    omega
  have hdis : Pairwise (fun j l => Disjoint (Y j) (Y l)) :=
    fun j l hjl => (hd (fun he => hjl (Subtype.ext he))).mono (hYsub j) (hYsub l)
  obtain ⟨f, hmem, hind⟩ := sparse_independent_transversal G Y hdis F
    (Nat.succ_pos _) hYcard
    (fun j l hjl u hu v hv => hcross j l (fun he => hjl (Subtype.ext he))
      u (hYsub j hu) v (hYsub l hv)) (Nat.lt_succ_sqrt' F.card)
  let I := univ.image f
  have hf : Function.Injective f := by
    intro j l he
    by_contra hn
    exact disjoint_left.mp (hdis hn) (hmem j) (he ▸ hmem l)
  have hi : G.IsIndepSet (I : Set V) := by
    intro u hu v hv huv
    obtain ⟨j, _, rfl⟩ := mem_image.mp hu
    obtain ⟨l, _, rfl⟩ := mem_image.mp hv
    exact hind j l (fun he => huv (congrArg f he))
  have hinfo {z : V} (hz : z ∈ I) :
      z ∈ S ∧ z ≠ x ∧ z ≠ y ∧ ¬G.Adj x z ∧ ¬G.Adj y z := by
    obtain ⟨j, _, rfl⟩ := mem_image.mp hz
    have h := hmem j
    obtain ⟨hzy, hz'⟩ := mem_erase.mp h
    obtain ⟨hzx, hz'⟩ := mem_erase.mp hz'
    obtain ⟨hz1, hz2⟩ := mem_inter.mp hz'
    exact ⟨hBS j (hYsub j h), hzx, hzy, (mem_filter.mp hz1).2, (mem_filter.mp hz2).2⟩
  have hxI : x ∉ I := fun hz => (hinfo hz).2.1 rfl
  have hyI : y ∉ insert x I := fun hz => (mem_insert.mp hz).elim hxy.symm
    (fun h => (hinfo h).2.2.1 rfl)
  have hIx := independent_insert_of_nonadjacent G hi x (fun _ hz => (hinfo hz).2.2.2.1)
  apply h.free (insert y (insert x I)) (insert_subset hyS (insert_subset hxS (fun _ hz => (hinfo hz).1)))
  refine ⟨independent_insert_of_nonadjacent G hIx y ?_, ?_⟩
  · intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact fun hadj => hnot hadj.symm
    · exact (hinfo hz).2.2.2.2
  · have hIcard : I.card + 1 = t := by
      simpa [I, card_image_of_injective _ hf, Fintype.card_coe, K, ht] using
        congrArg (· = t) (card_erase_add_one (mem_univ i))
    rw [card_insert_of_notMem hyI, card_insert_of_notMem hxI]
    omega

theorem clique_misses_at_most_one {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {A : Finset V} (hcl : G.IsClique (A : Set V)) {x : V} (hx : x ∈ A) :
    (A.filter (fun y => ¬G.Adj x y)).card ≤ 1 := by
  have hsub : A.filter (fun y => ¬G.Adj x y) ⊆ {x} := by
    intro y hy
    obtain ⟨hyA, hn⟩ := mem_filter.mp hy
    exact mem_singleton.mpr (by by_contra h; exact hn (hcl hx hyA (Ne.symm h)))
  simpa using card_le_card hsub

variable {V ι : Type*} [DecidableEq V] [Fintype ι]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (B : ι → Finset V) (S : Finset V)
variable {q v : ℕ}

/-- A vertex from the original blocks can be assigned only to a block containing
it, since it misses at most itself in every clique containing it. -/
theorem singleBlock_subset_original_union_exceptions
    (hcl : ∀ i, G.IsClique (B i : Set V)) (hq : 1 ≤ q) (i : ι) :
    singleBlock G B q S i ⊆ B i ∪ (S \ univ.biUnion B) := by
  classical
  intro x hx
  obtain ⟨hxS, _, hfar⟩ := (mem_singleBlock G).mp hx
  by_cases h : x ∈ univ.biUnion B
  · obtain ⟨j, _, hj⟩ := mem_biUnion.mp h
    have heq : j = i := by
      by_contra hji
      exact (not_lt_of_ge ((clique_misses_at_most_one G (hcl j) hj).trans hq)) (hfar j hji)
    exact mem_union_left _ (heq ▸ hj)
  · exact mem_union_right _ (mem_sdiff.mpr ⟨hxS,h⟩)

theorem singleBlock_missed_le (hcl : ∀ i, G.IsClique (B i : Set V))
    (hq : 1 ≤ q) (i : ι) (x : V) :
    ((singleBlock G B q S i).filter (fun y => ¬G.Adj x y)).card ≤
      ((B i).filter (fun y => ¬G.Adj x y)).card + (S \ univ.biUnion B).card := by
  classical
  have hsub : (singleBlock G B q S i).filter (fun y => ¬G.Adj x y) ⊆
      ((B i).filter (fun y => ¬G.Adj x y)) ∪ (S \ univ.biUnion B) := by
    intro y hy
    obtain ⟨hy, hmiss⟩ := mem_filter.mp hy
    rcases mem_union.mp (singleBlock_subset_original_union_exceptions G B S hcl hq i hy)
      with hb | he
    · exact mem_union_left _ (mem_filter.mpr ⟨hb,hmiss⟩)
    · exact mem_union_right _ he
  exact (card_le_card hsub).trans (card_union_le ..)

private theorem other_close_of_unassigned (i : ι) (x : V)
    (hx : x ∈ S \ univ.biUnion (singleBlock G B q S))
    (hclose : ((B i).filter (fun y => ¬G.Adj x y)).card ≤ q) :
    ∃ j, j ≠ i ∧ ((B j).filter (fun y => ¬G.Adj x y)).card ≤ q := by
  classical
  by_contra! hall
  exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨i, mem_univ i,
    (mem_singleBlock G).mpr ⟨(mem_sdiff.mp hx).1, hclose, hall⟩⟩)

/-- An unassigned vertex lying in one original row must be close to another row. -/
theorem ambiguous_in_row_has_other (hcl : ∀ i, G.IsClique (B i : Set V)) (hq : 1 ≤ q)
    (i : ι) (x : V) (hx : x ∈ S \ univ.biUnion (singleBlock G B q S)) (hxi : x ∈ B i) :
    ∃ j, j ≠ i ∧ ((B j).filter (fun y => ¬G.Adj x y)).card ≤ q :=
  other_close_of_unassigned G B S i x hx ((clique_misses_at_most_one G (hcl i) hxi).trans hq)

/-- If every vertex is close to some original block, an unassigned vertex
is close to two different enlarged blocks, allowing for the exceptions. -/
theorem ambiguous_has_two_close_singles (hcl : ∀ i, G.IsClique (B i : Set V))
    (hq : 1 ≤ q) (hvq : v ≤ q)
    (hnear : ∀ x ∈ S, ∃ i, ((B i).filter (fun y => ¬G.Adj x y)).card ≤ v)
    (x : V) (hx : x ∈ S \ univ.biUnion (singleBlock G B q S)) :
    ∃ i j, i ≠ j ∧
      ((singleBlock G B q S i).filter (fun y => ¬G.Adj x y)).card ≤ v+(S \ univ.biUnion B).card ∧
      ((singleBlock G B q S j).filter (fun y => ¬G.Adj x y)).card ≤ q+(S \ univ.biUnion B).card := by
  obtain ⟨i, hi⟩ := hnear x (mem_sdiff.mp hx).1
  obtain ⟨j, hji, hj⟩ := other_close_of_unassigned G B S i x hx (hi.trans hvq)
  exact ⟨i,j,hji.symm, (singleBlock_missed_le G B S hcl hq i x).trans (Nat.add_le_add_right hi _),
    (singleBlock_missed_le G B S hcl hq j x).trans (Nat.add_le_add_right hj _)⟩

end Erdos617
