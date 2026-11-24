import Erdos617.RankBasic
import Erdos617.RankEdges
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Erdos617

open Finset

private noncomputable def incident {ι ε : Type*} (E : Finset ε)
    (touch : ε → ι → Prop) (J : Finset ι) : Finset ε := by
  classical
  exact E.filter fun e => ∃ i ∈ J, touch e i

private theorem mem_incident {ι ε : Type*} {E : Finset ε}
    {touch : ε → ι → Prop} {J : Finset ι} {e : ε} :
    e ∈ incident E touch J ↔ e ∈ E ∧ ∃ i ∈ J, touch e i := by
  classical
  simp [incident]

/-- If the total number of incident edges does not exceed the sum of
the capacities, some nonempty collection of parts can accommodate
every edge incident to that collection. -/
private theorem assign_incident {ι ε : Type*} [DecidableEq ι] [DecidableEq ε]
    (cap : ι → ℕ) (E : Finset ε) (touch : ε → ι → Prop) (P : Finset ι)
    (hp : P.Nonempty) (hbudget : (incident E touch P).card ≤ ∑ i ∈ P, cap i) :
    ∃ J ⊆ P, J.Nonempty ∧
      ∃ f : incident E touch J → Σ _ : ι, ℕ, Function.Injective f ∧
        ∀ e, (f e).1 ∈ J ∧ touch e (f e).1 ∧ (f e).2 < cap (f e).1 := by
  classical
  induction P using Finset.strongInductionOn with
  | _ P ih =>
    let W := incident E touch P
    let slots (e : W) : Finset (Σ _ : ι, ℕ) :=
      (P.filter (touch e)).sigma fun i => range (cap i)
    by_cases hh : ∀ B : Finset W, B.card ≤ (B.biUnion slots).card
    · obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' slots).mp hh
      refine ⟨P, Subset.rfl, hp, f, hfinj, fun e => ?_⟩
      obtain ⟨h1, h2⟩ := mem_sigma.mp (hf e)
      exact ⟨(mem_filter.mp h1).1, (mem_filter.mp h1).2, mem_range.mp h2⟩
    · obtain ⟨B, hB⟩ : ∃ B : Finset W, (B.biUnion slots).card < B.card := by
        simpa only [not_forall, not_le] using hh
      let M := P.filter fun i => ∃ e ∈ B, touch e i
      have hM : M ⊆ P := filter_subset .. 
      have hslots : B.biUnion slots = M.sigma (fun i => range (cap i)) := by
        ext ⟨i, k⟩
        simp only [slots, M, mem_biUnion, mem_sigma, mem_filter, mem_range]
        constructor
        · rintro ⟨e, he, ⟨hi, het⟩, hk⟩
          exact ⟨⟨hi, e, he, het⟩, hk⟩
        · rintro ⟨⟨hi, e, he, het⟩, hk⟩
          exact ⟨e, he, ⟨hi, het⟩, hk⟩
      rw [hslots, card_sigma] at hB
      simp only [card_range] at hB
      have hbW : B.card ≤ W.card := by simpa using (B.card_le_univ)
      let K := P \ M
      have hsum : (∑ i ∈ K, cap i) + ∑ i ∈ M, cap i = ∑ i ∈ P, cap i :=
        sum_sdiff hM
      have hBne : B.Nonempty := card_pos.mp (by omega)
      obtain ⟨e, he⟩ := hBne
      obtain ⟨i, hi, hit⟩ := (mem_filter.mp (show e.val ∈ incident E touch P from e.prop)).2
      have hKM : K ⊂ P := sdiff_ssubset hM ⟨i, mem_filter.mpr ⟨hi, e, he, hit⟩⟩
      have hKne : K.Nonempty := by
        by_contra hempty
        rw [not_nonempty_iff_eq_empty.mp hempty, sum_empty, zero_add] at hsum
        change W.card ≤ _ at hbudget
        omega
      have hEK : incident E touch K ⊆ W :=
        fun e he => by
          obtain ⟨he, i, hi, het⟩ := mem_filter.mp he
          exact mem_filter.mpr ⟨he, i, (mem_sdiff.mp hi).1, het⟩
      let B' := B.map (Function.Embedding.subtype (· ∈ W))
      have hB' : B' ⊆ W := by
        intro e he
        obtain ⟨b, _, rfl⟩ := mem_map.mp he
        exact b.prop
      have hd : Disjoint (incident E touch K) B' := by
        apply Finset.disjoint_left.mpr
        intro e h1 h2
        obtain ⟨b, hb, rfl⟩ := mem_map.mp h2
        obtain ⟨_, i, hi, ht⟩ := mem_filter.mp h1
        exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨(mem_sdiff.mp hi).1, b, hb, ht⟩)
      have hcnt := card_le_card (union_subset hEK hB')
      rw [card_union_of_disjoint hd, show B'.card = B.card from card_map ..] at hcnt
      have hb : (incident E touch K).card ≤ ∑ i ∈ K, cap i := by
        change W.card ≤ _ at hbudget
        omega
      obtain ⟨J, hJK, hJ, f, hf, ht⟩ := ih K hKM hKne hb
      exact ⟨J, hJK.trans hKM.subset, hJ, f, hf, ht⟩

/-- A capacitated assignment supplies one forbidden endpoint per boundary edge. -/
private theorem forbid_incident {V : Type*} [DecidableEq V] (cap : Finset V → ℕ)
    (E : Finset (Sym2 V)) (P : Finset (Finset V)) (hP : P.Nonempty)
    (hb : E.card ≤ ∑ A ∈ P, cap A) :
    ∃ J ⊆ P, J.Nonempty ∧ ∃ D : Finset V → Finset V,
      (∀ A, D A ⊆ A ∧ (D A).card ≤ cap A) ∧
      ∀ e ∈ E, (∃ A ∈ J, ∃ x ∈ A, x ∈ e) → ∃ A ∈ J, ∃ x ∈ D A, x ∈ e := by
  classical
  let touch (e : Sym2 V) (A : Finset V) := ∃ x ∈ A, x ∈ e
  have hle : (incident E touch P).card ≤ E.card := card_le_card fun _ h => (mem_incident.mp h).1
  obtain ⟨J, hJP, hJ, f, hinj, hf⟩ := assign_incident cap E touch P hP (hle.trans hb)
  let W := incident E touch J
  choose x hx hxedge using fun e : W => (hf e).2.1
  let own (A : Finset V) := (univ : Finset W).filter fun e => (f e).1 = A
  let D (A : Finset V) := (own A).image x
  refine ⟨J, hJP, hJ, D, ?_, ?_⟩
  · intro A
    have ho (e : W) (he : e ∈ own A) : (f e).1 = A := (mem_filter.mp he).2
    refine ⟨?_, card_image_le.trans ?_⟩
    · intro z hz
      obtain ⟨e, he, rfl⟩ := mem_image.mp hz
      simpa [ho e he] using hx e
    · have hcount : (own A).card ≤ (range (cap A)).card := by
        apply card_le_card_of_injOn (fun e : W => (f e).2)
        · intro e he
          exact mem_range.mpr (by simpa [ho e he] using (hf e).2.2)
        · intro e he e' he' heq
          apply hinj
          exact Sigma.ext ((ho e he).trans (ho e' he').symm) (heq_of_eq heq)
      simpa using hcount
  · intro e he ht
    let w : W := ⟨e, mem_incident.mpr ⟨he, ht⟩⟩
    exact ⟨(f w).1, (hf w).1, x w, mem_image.mpr ⟨w, by simp [own], rfl⟩, hxedge w⟩

open SimpleGraph

/-- Rank inseparability forces more boundary edges than the total capacities
given by the minimum blockers of the parts after deleting one vertex. -/
theorem rank_boundary {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hS : RankInseparable G S) {v : V} (hv : v ∈ S)
    (P : Finset (Finset V)) (hP : P.Nonempty) (hu : P.biUnion id = S.erase v)
    (hd : (P : Set (Finset V)).PairwiseDisjoint id)
    (hi : ∀ A ∈ P, RankInseparable G A)
    (_hs : ∑ A ∈ P, rankOn G A = rankOn G (S.erase v)) :
    (∑ A ∈ P, blockEdges G A) + (∑ A ∈ P, blockerSize G A) + 1 ≤
      blockEdges G S + P.card := by
  classical
  let cap (A : Finset V) := blockerSize G A - 1
  let E := inducedEdgeSet G S \ P.biUnion (inducedEdgeSet G)
  have hcover : P.biUnion id ⊆ S := hu ▸ erase_subset v S
  have hcap : (∑ A ∈ P, cap A) + P.card = ∑ A ∈ P, blockerSize G A := by
    calc
      _ = ∑ A ∈ P, (cap A + 1) := by simp [sum_add_distrib]
      _ = _ := sum_congr rfl fun A hA => by
        have h := blockerSize_pos G (hi A hA).nonempty
        dsimp [cap]
        omega
  have he := boundary_edge_count G S P hcover hd
  change E.card + _ = _ at he
  by_contra! hsmall
  have hbudget : E.card ≤ ∑ A ∈ P, cap A := by omega
  obtain ⟨J, hJP, hJ, D, hD, hforbid⟩ := forbid_incident cap E P hP hbudget
  let U := J.biUnion id
  have hAS {A : Finset V} (hA : A ∈ J) : A ⊆ U :=
    fun _ h => mem_biUnion.mpr ⟨A, hA, h⟩
  have hU : U ⊆ S.erase v := by
    intro x hx
    obtain ⟨A, hA, ha⟩ := mem_biUnion.mp hx
    exact hu ▸ (mem_biUnion.mpr ⟨A, hJP hA, ha⟩)
  have hUS : U ⊆ S := hU.trans (erase_subset ..)
  have hUn : U.Nonempty := by
    obtain ⟨A, hA⟩ := hJ
    exact (hi A (hJP hA)).nonempty.mono (hAS hA)
  have hTn : (S \ U).Nonempty := ⟨v, mem_sdiff.mpr ⟨hv, fun h => notMem_erase v S (hU h)⟩⟩
  have hdistinct {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) {z : V}
      (ha : z ∈ A) (hb : z ∈ B) : A = B := by
    by_contra hh
    exact Finset.disjoint_left.mp (hd hA hB hh) ha hb
  have hchoices (A : Finset V) : ∃ M : Finset V, A ∈ J →
      M ⊆ A ∧ G.IsIndepSet (M : Set V) ∧ M.card = rankOn G A ∧ Disjoint M (D A) := by
    by_cases hA : A ∈ J
    · have hpos := blockerSize_pos G (hi A (hJP hA)).nonempty
      have hbound := (hD A).2
      dsimp [cap] at hbound
      obtain ⟨M, hM⟩ := exists_max_indep_disjoint_of_card_lt G (hD A).1 (by omega)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨∅, fun h => (hA h).elim⟩
  choose M hM using hchoices
  obtain ⟨Y, hYT, hYind, hYcard⟩ := exists_max_indep G (S \ U)
  let W := J.biUnion M ∪ Y
  have hMU : J.biUnion M ⊆ U := by
    intro z hz
    obtain ⟨A, hA, h⟩ := mem_biUnion.mp hz
    exact hAS hA ((hM A hA).1 h)
  have hWS : W ⊆ S := union_subset (hMU.trans hUS) (hYT.trans sdiff_subset)
  have hlocal {A : Finset V} (hA : A ∈ J) {z : V} (hz : z ∈ W) (ha : z ∈ A) : z ∈ M A := by
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨B, hB, hz⟩ := mem_biUnion.mp hz
      have heq := hdistinct (hJP hB) (hJP hA) ((hM B hB).1 hz) ha
      exact heq ▸ hz
    · exact ((mem_sdiff.mp (hYT hz)).2 (hAS hA ha)).elim
  have havoid {A : Finset V} (hA : A ∈ J) {z : V} (hz : z ∈ W) (ha : z ∈ D A) : False :=
    Finset.disjoint_left.mp (hM A hA).2.2.2 (hlocal hA hz ((hD A).1 ha)) ha
  have hcross {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hadj : G.Adj x y)
      {A : Finset V} (hA : A ∈ J) (hxa : x ∈ A) : False := by
    by_cases hinner : s(x,y) ∈ P.biUnion (inducedEdgeSet G)
    · obtain ⟨B, hB, hxy⟩ := mem_biUnion.mp hinner
      obtain ⟨hxB, hyB, _⟩ := (mem_inducedEdgeSet G).mp hxy
      have hab := hdistinct hB (hJP hA) hxB hxa
      exact (hM A hA).2.1 (hlocal hA hx hxa) (hlocal hA hy (hab ▸ hyB)) hadj.ne hadj
    · have heE : s(x,y) ∈ E := mem_sdiff.mpr
        ⟨(mem_inducedEdgeSet G).mpr ⟨hWS hx, hWS hy, hadj⟩, hinner⟩
      obtain ⟨B, hB, z, hzD, hze⟩ := hforbid _ heE ⟨A, hA, x, hxa, by simp⟩
      rcases Sym2.mem_iff'.mp hze with rfl | rfl
      · exact havoid hB hx hzD
      · exact havoid hB hy hzD
  have hWind : G.IsIndepSet (W : Set V) := by
    intro x hx y hy hne hadj
    rcases mem_union.mp hx with hx' | hx'
    · obtain ⟨A, hA, hxA⟩ := mem_biUnion.mp hx'
      exact hcross hx hy hadj hA ((hM A hA).1 hxA)
    · rcases mem_union.mp hy with hy' | hy'
      · obtain ⟨A, hA, hyA⟩ := mem_biUnion.mp hy'
        exact hcross hy hx hadj.symm hA ((hM A hA).1 hyA)
      · exact hYind hx' hy' hne hadj
  have hdM : (J : Set (Finset V)).PairwiseDisjoint M :=
    fun A ha B hb hab => (hd (hJP ha) (hJP hb) hab).mono (hM A ha).1 (hM B hb).1
  have hdY : Disjoint (J.biUnion M) Y := disjoint_sdiff.mono hMU hYT
  have hcard : W.card = (∑ A ∈ J, rankOn G A) + rankOn G (S \ U) := by
    rw [show W = J.biUnion M ∪ Y from rfl, card_union_of_disjoint hdY, card_biUnion hdM, hYcard]
    exact congrArg (· + rankOn G (S \ U)) (sum_congr rfl fun A hA => (hM A hA).2.2.1)
  have hbound := card_le_rankOn G hWS hWind
  have hsum := rankOn_biUnion_le G J
  change rankOn G U ≤ _ at hsum
  have hstrict := hS.lt_of_partition hUn hTn disjoint_sdiff (union_sdiff_of_subset hUS)
  omega

end Erdos617
