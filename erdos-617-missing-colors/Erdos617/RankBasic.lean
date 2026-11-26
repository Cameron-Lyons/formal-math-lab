module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*}

/-- Maximum cardinality of an independent subset of a finite vertex set. -/
noncomputable def rankOn (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (S.powerset.filter fun I : Finset V => G.IsIndepSet (I : Set V)).sup card

theorem exists_max_indep (G : SimpleGraph V) (S : Finset V) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ I.card = rankOn G S := by
  classical
  let F := S.powerset.filter fun I : Finset V => G.IsIndepSet (I : Set V)
  have he : G.IsIndepSet ((∅ : Finset V) : Set V) := by
    rw [coe_empty]
    exact Set.pairwise_empty _
  have hF : F.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), he⟩⟩
  obtain ⟨I, hI, hcard⟩ := exists_mem_eq_sup F hF card
  obtain ⟨hIS, hind⟩ := mem_filter.mp hI
  exact ⟨I, mem_powerset.mp hIS, hind, hcard.symm⟩

theorem card_le_rankOn (G : SimpleGraph V) {I A : Finset V} (hI : I ⊆ A)
    (hi : G.IsIndepSet (I : Set V)) : I.card ≤ rankOn G A := by
  classical
  exact le_sup (f := card) (mem_filter.mpr ⟨mem_powerset.mpr hI, hi⟩)

theorem rankOn_mono (G : SimpleGraph V) {A B : Finset V} (h : A ⊆ B) :
    rankOn G A ≤ rankOn G B := by
  obtain ⟨I, hIA, hi, hcard⟩ := exists_max_indep G A
  rw [← hcard]
  exact card_le_rankOn G (hIA.trans h) hi

theorem rankOn_le_card (G : SimpleGraph V) (S : Finset V) : rankOn G S ≤ S.card := by
  obtain ⟨I, hI, _, hcard⟩ := exists_max_indep G S
  rw [← hcard]
  exact card_le_card hI

@[simp] theorem rankOn_empty (G : SimpleGraph V) : rankOn G ∅ = 0 := by
  simpa using rankOn_le_card G ∅

@[simp] theorem rankOn_singleton (G : SimpleGraph V) (x : V) : rankOn G {x} = 1 := by
  have hi : G.IsIndepSet (({x} : Finset V) : Set V) := by
    rw [coe_singleton]
    exact Set.pairwise_singleton _ _
  have lower := card_le_rankOn G (show ({x} : Finset V) ⊆ {x} from Subset.rfl) hi
  have upper := rankOn_le_card G {x}
  simp only [card_singleton] at lower upper
  omega

theorem rankOn_pos (G : SimpleGraph V) {S : Finset V} (hs : S.Nonempty) :
    0 < rankOn G S := by
  obtain ⟨x, hx⟩ := hs
  have h := rankOn_mono G (singleton_subset_iff.mpr hx)
  rw [rankOn_singleton] at h
  omega

variable [DecidableEq V]

theorem rankOn_union_le (G : SimpleGraph V) (A B : Finset V) :
    rankOn G (A ∪ B) ≤ rankOn G A + rankOn G B := by
  obtain ⟨I, hI, hi, hcard⟩ := exists_max_indep G (A ∪ B)
  rw [← hcard]
  have ha := card_le_rankOn G (inter_subset_right (s₁ := I) (s₂ := A))
    (hi.mono (inter_subset_left (s₁ := I) (s₂ := A)))
  have hb : I \ A ⊆ B := by
    intro x hx
    obtain ⟨hxI, hxA⟩ := mem_sdiff.mp hx
    exact (mem_union.mp (hI hxI)).resolve_left hxA
  have hc := card_le_rankOn G hb (hi.mono sdiff_subset)
  have := card_inter_add_card_sdiff I A
  omega

theorem rankOn_biUnion_le (G : SimpleGraph V) (P : Finset (Finset V)) :
    rankOn G (P.biUnion id) ≤ ∑ A ∈ P, rankOn G A := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert A P ha ih =>
    rw [biUnion_insert, sum_insert ha]
    exact (rankOn_union_le G _ _).trans (Nat.add_le_add_left ih _)

/-- A nonempty set is inseparable if splitting it into two nonempty parts
strictly increases the sum of their independence ranks. -/
structure RankInseparable (G : SimpleGraph V) (S : Finset V) : Prop where
  nonempty : S.Nonempty
  lt_of_partition : ∀ {A B : Finset V}, A.Nonempty → B.Nonempty → Disjoint A B →
    A ∪ B = S → rankOn G S < rankOn G A + rankOn G B

theorem RankInseparable.rank_pos {G : SimpleGraph V} {S : Finset V}
    (h : RankInseparable G S) : 0 < rankOn G S := rankOn_pos G h.nonempty

theorem RankInseparable.rank_erase {G : SimpleGraph V} {S : Finset V}
    (h : RankInseparable G S) {v : V} (hv : v ∈ S) (hcard : 1 < S.card) :
    rankOn G (S.erase v) = rankOn G S := by
  have hc := card_erase_add_one hv
  have he : (S.erase v).Nonempty := card_pos.mp (by omega)
  have hu : ({v} : Finset V) ∪ S.erase v = S := by simpa using insert_erase hv
  have hh := h.lt_of_partition (singleton_nonempty v) he (by simp) hu
  rw [rankOn_singleton] at hh
  exact le_antisymm (rankOn_mono G (erase_subset _ _)) (by omega)

theorem exists_rank_partition (G : SimpleGraph V) (S : Finset V) :
    ∃ P : Finset (Finset V), P.biUnion id = S ∧ (P : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ A ∈ P, RankInseparable G A) ∧ ∑ A ∈ P, rankOn G A = rankOn G S := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hne : S.Nonempty
    · by_cases hin : RankInseparable G S
      · exact ⟨{S}, by simp, by simp, by simpa using hin, by simp⟩
      · have hsplit : ¬ ∀ {A B : Finset V}, A.Nonempty → B.Nonempty → Disjoint A B →
            A ∪ B = S → rankOn G S < rankOn G A + rankOn G B :=
          fun h => hin ⟨hne, h⟩
        push Not at hsplit
        obtain ⟨A, B, ha, hb, hd, hu, hge⟩ := hsplit
        subst S
        have smaller {X Y : Finset V} (hy : Y.Nonempty) (hxy : Disjoint X Y) :
            X ⊂ X ∪ Y := by
          obtain ⟨y, hy⟩ := hy
          exact (ssubset_iff_of_subset subset_union_left).mpr
            ⟨y, mem_union_right _ hy, fun hx => disjoint_left.mp hxy hx hy⟩
        obtain ⟨P, hP, hdP, hiP, hsP⟩ := ih A (smaller hb hd)
        obtain ⟨Q, hQ, hdQ, hiQ, hsQ⟩ := ih B (by simpa [union_comm] using smaller ha hd.symm)
        have cross {X Y : Finset V} (hx : X ∈ P) (hy : Y ∈ Q) : Disjoint X Y :=
          hd.mono (biUnion_subset.mp hP.le X hx) (biUnion_subset.mp hQ.le Y hy)
        have hpq : Disjoint P Q := by
          refine disjoint_left.mpr fun X hx hy => ?_
          obtain ⟨x, hxX⟩ := (hiP X hx).nonempty
          exact disjoint_left.mp (cross hx hy) hxX hxX
        refine ⟨P ∪ Q, by rw [union_biUnion, hP, hQ], ?_, ?_, ?_⟩
        · rw [coe_union]
          exact hdP.union hdQ fun _ hx _ hy _ => cross hx hy
        · intro X hx
          exact (mem_union.mp hx).elim (hiP X) (hiQ X)
        · rw [sum_union hpq, hsP, hsQ]
          exact le_antisymm hge (rankOn_union_le G A B)
    · rw [not_nonempty_iff_eq_empty.mp hne]
      exact ⟨∅, by simp, by simp, by simp, by simp⟩

def IsBlocker (G : SimpleGraph V) (A H : Finset V) : Prop :=
  H ⊆ A ∧ ∀ I ⊆ A, G.IsIndepSet (I : Set V) → I.card = rankOn G A → (I ∩ H).Nonempty

theorem exists_blocker_card (G : SimpleGraph V) {A : Finset V} (hA : A.Nonempty) :
    ∃ k : ℕ, ∃ H : Finset V, H.card = k ∧ IsBlocker G A H := by
  refine ⟨A.card, A, rfl, Subset.rfl, fun I hI _ hi => ?_⟩
  rw [inter_eq_left.mpr hI]
  exact card_pos.mp (hi ▸ rankOn_pos G hA)

/-- Least cardinality of a subset hitting every maximum independent subset.
The empty vertex set has blocker size zero by convention. -/
noncomputable def blockerSize (G : SimpleGraph V) (A : Finset V) : ℕ := by
  classical
  exact if hA : A.Nonempty then Nat.find (exists_blocker_card G hA) else 0

theorem exists_min_blocker (G : SimpleGraph V) {A : Finset V} (hA : A.Nonempty) :
    ∃ H ⊆ A, H.card = blockerSize G A ∧
      ∀ I ⊆ A, G.IsIndepSet (I : Set V) → I.card = rankOn G A → (I ∩ H).Nonempty := by
  classical
  rw [blockerSize, dite_eq_left hA]
  obtain ⟨H, hh, hsub, hhit⟩ := Nat.find_spec (exists_blocker_card G hA)
  exact ⟨H, hsub, hh, hhit⟩

theorem blockerSize_pos (G : SimpleGraph V) {A : Finset V} (hA : A.Nonempty) :
    0 < blockerSize G A := by
  obtain ⟨H, _, hcard, hh⟩ := exists_min_blocker G hA
  rw [← hcard]
  obtain ⟨I, hI, hi, hr⟩ := exists_max_indep G A
  obtain ⟨x, hx⟩ := hh I hI hi hr
  exact card_pos.mpr ⟨x, (mem_inter.mp hx).2⟩

theorem exists_max_indep_disjoint_of_card_lt (G : SimpleGraph V) {A H : Finset V}
    (hHA : H ⊆ A) (hlt : H.card < blockerSize G A) :
    ∃ I ⊆ A, G.IsIndepSet (I : Set V) ∧ I.card = rankOn G A ∧ Disjoint I H := by
  classical
  by_cases hA : A.Nonempty
  · rw [blockerSize, dite_eq_left hA] at hlt
    by_contra! hn
    have hh : IsBlocker G A H := by
      refine ⟨hHA, fun I hI hi hr => ?_⟩
      by_contra he
      exact hn I hI hi hr (Finset.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp he))
    exact (Nat.not_le_of_lt hlt) (Nat.find_min' (exists_blocker_card G hA) ⟨H, rfl, hh⟩)
  · simp [blockerSize, hA] at hlt

end Erdos617
