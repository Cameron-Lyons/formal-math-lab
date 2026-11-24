import Erdos617.RankBasic
import Erdos617.RankEdges
import Erdos617.IndependentSets

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {S A : Finset V} {G : SimpleGraph V}

/-- An additive decomposition would result if there were no edge across this cut. -/
private theorem crossing_edge_of_inseparable (h : RankInseparable G S) {A B : Finset V}
    (ha : A.Nonempty) (hb : B.Nonempty) (hd : Disjoint A B) (hu : A ∪ B = S) :
    ∃ x ∈ A, ∃ y ∈ B, G.Adj x y := by
  classical
  by_contra! hn
  obtain ⟨I, hIA, hi, hIcard⟩ := exists_max_indep G A
  obtain ⟨J, hJB, hj, hJcard⟩ := exists_max_indep G B
  have hIJ : G.IsIndepSet (I ∪ J : Finset V) := by
    intro x hx y hy hxy e
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact hi hx hy hxy e
    · exact hn x (hIA hx) y (hJB hy) e
    · exact hn y (hIA hy) x (hJB hx) e.symm
    · exact hj hx hy hxy e
  have hl := card_le_rankOn G (hu ▸ Finset.union_subset_union hIA hJB) hIJ
  rw [card_union_of_disjoint (hd.mono hIA hJB), hIcard, hJcard] at hl
  exact (h.lt_of_partition ha hb hd hu).not_ge hl

/-- A rank-inseparable set of maximum degree at most D has order at most Dα+1.
Every proper residual set has a vertex incident to an edge leaving it. -/
theorem exists_degree_ge_of_inseparable [DecidableRel G.Adj] (h : RankInseparable G S)
    (d : ℕ) (hbig : (d-1)*rankOn G S + 1 < S.card) (hd : 1 ≤ d) :
    ∃ v ∈ S, d ≤ (S.filter (G.Adj v)).card := by
  classical
  by_contra! hdeg
  let D := d-1
  have cover (R : Finset V) (hR : R ⊂ S) :
      ∃ I ⊆ R, G.IsIndepSet I ∧ R.card ≤ D*I.card := by
    induction R using Finset.strongInductionOn with
    | _ R ih =>
      by_cases hr : R.Nonempty
      · obtain ⟨x, hx, y, hy, hxy⟩ := crossing_edge_of_inseparable h hr
          (sdiff_nonempty.mpr (not_subset.mpr (by
            obtain ⟨y, hy, hnot⟩ := Finset.exists_of_ssubset hR
            exact ⟨y, hy, hnot⟩)))
          disjoint_sdiff (union_sdiff_of_subset hR.le)
        have hlt : (R.filter (G.Adj x)).card < (S.filter (G.Adj x)).card := by
          apply card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset_filter _ hR.le, ?_⟩
          intro he
          have hyS : y ∈ S.filter (G.Adj x) := mem_filter.mpr ⟨(mem_sdiff.mp hy).1, hxy⟩
          exact (mem_sdiff.mp hy).2 (mem_filter.mp (he ▸ hyS)).1
        let N := insert x (R.filter (G.Adj x))
        have hNR : N ⊆ R := insert_subset hx (filter_subset ..)
        have hN : N.card ≤ D := by
          have he := hdeg x (hR.le hx)
          have hc : N.card = (R.filter (G.Adj x)).card+1 := by simp [N]
          dsimp [D]
          omega
        let T := R \ N
        have hTR : T ⊂ R := sdiff_ssubset hNR ⟨x, mem_insert_self ..⟩
        obtain ⟨I, hIT, hi, hcount⟩ := ih T hTR (hTR.trans hR)
        have hIR : I ⊆ R := hIT.trans sdiff_subset
        have hxI : x ∉ I := fun hxi => (mem_sdiff.mp (hIT hxi)).2 (mem_insert_self ..)
        refine ⟨insert x I, insert_subset hx hIR, independent_insert_of_nonadjacent G hi x ?_, ?_⟩
        · intro z hz hzx
          exact (mem_sdiff.mp (hIT hz)).2 (mem_insert_of_mem (mem_filter.mpr ⟨hIR hz,hzx⟩))
        · have he : T.card+N.card = R.card := Finset.card_sdiff_add_card_eq_card hNR
          rw [card_insert_of_notMem hxI, Nat.mul_succ]
          omega
      · rw [not_nonempty_iff_eq_empty.mp hr]
        exact ⟨∅, Subset.rfl, by simp [IsIndepSet], by simp⟩
  obtain ⟨v, hv⟩ := h.nonempty
  obtain ⟨I, hI, hi, hc⟩ := cover (S.erase v) (erase_ssubset hv)
  have hbound := Nat.mul_le_mul_left D (card_le_rankOn G (hI.trans (erase_subset ..)) hi)
  have := card_erase_add_one hv
  change D*rankOn G S + 1 < S.card at hbig
  omega

omit [DecidableEq V] in
private theorem rankOn_congr_local (G K : SimpleGraph V) (A : Finset V)
    (h : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y ↔ K.Adj x y) : rankOn G A = rankOn K A := by
  apply Nat.le_antisymm
  · obtain ⟨I, hIA, hi, he⟩ := exists_max_indep G A
    exact he ▸ card_le_rankOn K hIA
      (fun x hx y hy hxy hK => hi hx hy hxy ((h x (hIA hx) y (hIA hy)).mpr hK))
  · obtain ⟨I, hIA, hi, he⟩ := exists_max_indep K A
    exact he ▸ card_le_rankOn G hIA
      (fun x hx y hy hxy hG => hi hx hy hxy ((h x (hIA hx) y (hIA hy)).mp hG))

/-- Attach a vertex to a smallest set meeting all maximum independent sets of A.
This preserves both the independence number and strictness on every partition. -/
theorem augment_inseparable_on [DecidableRel G.Adj] (ha : RankInseparable G A) (v : V)
    (hv : v ∉ A) :
    ∃ K : SimpleGraph V, ∃ _ : DecidableRel K.Adj, RankInseparable K (insert v A) ∧
      rankOn K (insert v A) = rankOn G A ∧
      blockEdges K (insert v A) = blockEdges G A + blockerSize G A ∧
      (∀ x ∈ A, ∀ y ∈ A, K.Adj x y ↔ G.Adj x y) := by
  classical
  obtain ⟨H, hHA, hsize, hit⟩ := exists_min_blocker G ha.nonempty
  let K : SimpleGraph V := {
    Adj := fun x y => (x ∈ A ∧ y ∈ A ∧ G.Adj x y) ∨ (x = v ∧ y ∈ H) ∨ (y = v ∧ x ∈ H)
    symm := by
      constructor
      intro x y h
      rcases h with h | h | h
      · exact Or.inl ⟨h.2.1,h.1,h.2.2.symm⟩
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    loopless := by
      constructor
      intro x h
      rcases h with h | ⟨rfl,h⟩ | ⟨rfl,h⟩
      · exact h.2.2.ne rfl
      · exact hv (hHA h)
      · exact hv (hHA h) }
  let instK : DecidableRel K.Adj := Classical.decRel _
  have same {x y : V} (hx : x ∈ A) (hy : y ∈ A) : G.Adj x y ↔ K.Adj x y := by
    constructor
    · exact fun e => Or.inl ⟨hx,hy,e⟩
    · rintro (e | ⟨rfl,_⟩ | ⟨rfl,_⟩)
      · exact e.2.2
      · exact (hv hx).elim
      · exact (hv hy).elim
  have rlocal {B : Finset V} (hB : B ⊆ A) : rankOn G B = rankOn K B :=
    rankOn_congr_local G K B fun _ hx _ hy => same (hB hx) (hB hy)
  have spoke {y : V} (hy : y ∈ A) : K.Adj v y ↔ y ∈ H := by simp [K,hv,ne_of_mem_of_not_mem hy hv]
  have rankeq : rankOn K (insert v A) = rankOn G A := by
    apply le_antisymm _ ((rlocal Subset.rfl).trans_le (rankOn_mono K (subset_insert v A)))
    obtain ⟨I, hIS, hi, hI⟩ := exists_max_indep K (insert v A)
    rw [← hI]
    by_cases hvi : v ∈ I
    · have hIA : I.erase v ⊆ A := fun _ hz =>
        (mem_insert.mp (hIS (mem_of_mem_erase hz))).resolve_left (mem_erase.mp hz).1
      have hsub := hi.mono (show (↑(I.erase v) : Set V) ⊆ ↑I from erase_subset ..)
      have hg : G.IsIndepSet (I.erase v) := fun _ hx _ hy hxy e =>
        hsub hx hy hxy ((same (hIA hx) (hIA hy)).mp e)
      have hc := card_le_rankOn G hIA hg
      have hne : (I.erase v).card ≠ rankOn G A := by
        intro he
        obtain ⟨y,hy⟩ := hit (I.erase v) hIA hg he
        obtain ⟨hyI,hyH⟩ := mem_inter.mp hy
        exact hi hvi (mem_of_mem_erase hyI) (mem_erase.mp hyI).1.symm ((spoke (hHA hyH)).mpr hyH)
      have := card_erase_add_one hvi
      omega
    · have hIA : I ⊆ A := fun z hz => (mem_insert.mp (hIS hz)).resolve_left (fun e => hvi (e ▸ hz))
      exact (card_le_rankOn K hIA hi).trans_eq (rlocal Subset.rfl).symm
  refine ⟨K, instK, ⟨⟨v,mem_insert_self ..⟩, ?_⟩, rankeq, ?_, fun _ hx _ hy => (same hx hy).symm⟩
  · intro X Y hx hy dis cov
    let X' := X ∩ A
    let Y' := Y ∩ A
    have hcover : X' ∪ Y' = A := by
      ext z
      have hz := congrArg (fun B : Finset V => z ∈ B) cov
      simp only [mem_union, mem_insert] at hz
      simp only [X',Y',mem_union,mem_inter]
      tauto
    have hdis : Disjoint X' Y' := dis.mono inter_subset_left inter_subset_left
    have hX := (rlocal (show X' ⊆ A from inter_subset_right)).trans_le
      (rankOn_mono K (show X' ⊆ X from inter_subset_left))
    have hY := (rlocal (show Y' ⊆ A from inter_subset_right)).trans_le
      (rankOn_mono K (show Y' ⊆ Y from inter_subset_left))
    rw [rankeq]
    by_cases hXne : X'.Nonempty
    · by_cases hYne : Y'.Nonempty
      · exact (ha.lt_of_partition hXne hYne hdis hcover).trans_le (Nat.add_le_add hX hY)
      · have he : X' = A := by simpa [not_nonempty_iff_eq_empty.mp hYne] using hcover
        obtain ⟨y,hyY⟩ := hy
        have hp := card_le_rankOn K (singleton_subset_iff.mpr hyY)
          (show K.IsIndepSet ({y} : Finset V) by simp [IsIndepSet])
        rw [card_singleton] at hp
        rw [he] at hX
        omega
    · have he : Y' = A := by simpa [not_nonempty_iff_eq_empty.mp hXne] using hcover
      obtain ⟨x,hxX⟩ := hx
      have hp := card_le_rankOn K (singleton_subset_iff.mpr hxX)
        (show K.IsIndepSet ({x} : Finset V) by simp [IsIndepSet])
      rw [card_singleton] at hp
      rw [he] at hY
      omega
  · have hloc : blockEdges K A = blockEdges G A := by
      rw [← card_inducedEdgeSet K, ← card_inducedEdgeSet G]
      congr 1
      ext e
      induction e using Sym2.inductionOn with
      | _ x y =>
        simp only [mem_inducedEdgeSet]
        exact and_congr_right fun hx => and_congr_right fun hy => (same hx hy).symm
    have hf : A.filter (K.Adj v) = H := by
      ext y
      simp only [mem_filter]
      exact ⟨fun h => (spoke h.1).mp h.2, fun h => ⟨hHA h,(spoke (hHA h)).mpr h⟩⟩
    have hsing : blockEdges K {v} = 0 := by
      have hc := (K.induce (↑({v} : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
      change blockEdges K {v} ≤ (Fintype.card ({v} : Finset V)).choose 2 at hc
      simpa using hc
    rw [← singleton_union, blockEdges_union K (disjoint_singleton_left.mpr hv), hsing,
      sum_singleton, hf, hloc, hsize]
    omega

theorem augment_inseparable [DecidableRel G.Adj] (ha : RankInseparable G A) (v : V)
    (hv : v ∉ A) :
    ∃ K : SimpleGraph V, ∃ _ : DecidableRel K.Adj, RankInseparable K (insert v A) ∧
      rankOn K (insert v A) = rankOn G A ∧
      blockEdges K (insert v A) = blockEdges G A + blockerSize G A := by
  obtain ⟨K, hdec, hK, hr, he, _⟩ := augment_inseparable_on ha v hv
  exact ⟨K, hdec, hK, hr, he⟩

end Erdos617
