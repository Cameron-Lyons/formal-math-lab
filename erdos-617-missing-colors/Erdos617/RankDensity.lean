import Erdos617.RankAugment
import Erdos617.RankBoundary
import Mathlib.Tactic.Ring

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

theorem blockEdges_erase_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) (hv : v ∈ S) :
    blockEdges G (S.erase v) + (S.filter (G.Adj v)).card = blockEdges G S := by
  have hd : Disjoint ({v} : Finset V) (S.erase v) := by simp
  have he := blockEdges_union G hd
  have hsingle : blockEdges G {v} = 0 := by
    have h := (G.induce (↑({v} : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
    change blockEdges G {v} ≤ (Fintype.card ({v} : Finset V)).choose 2 at h
    simpa using h
  simpa [hsingle, filter_erase, erase_eq_of_notMem, insert_erase hv, Nat.add_comm] using he.symm

theorem strict_part_card {R : Finset V} {P : Finset (Finset V)}
    (hu : P.biUnion id = R) (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hne : ∀ A ∈ P, A.Nonempty) (hm : P.card ≠ 1) (A : Finset V) (hA : A ∈ P) :
    A.card < R.card := by
  have sub (B : Finset V) (hB : B ∈ P) : B ⊆ R :=
    (biUnion_subset.mp hu.le) B hB
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨sub A hA, ?_⟩
  rintro rfl
  apply hm
  suffices P = {A} by simp [this]
  ext B
  simp only [mem_singleton]
  refine ⟨?_, fun he => he ▸ hA⟩
  intro hB
  by_contra hBA
  obtain ⟨z,hz⟩ := hne B hB
  exact disjoint_left.mp (hd hB hA hBA) hz (sub B hB hz)

/-- Every inseparable part satisfies each linear supporting inequality of the
refined Turán bound. This is the graph case of the edge estimate in
[Didin, Theorem 3](https://zenodo.org/records/22831382). -/
theorem rank_density (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (h : RankInseparable G S) (d : ℕ) :
    d*S.card ≤ blockEdges G S + (d.choose 2+1)*rankOn G S + (d-1) := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing G S d with
  | h n ih =>
    subst n
    induction d with
    | zero => simp
    | succ d lower =>
      have hp : 1 ≤ rankOn G S := h.rank_pos
      by_cases small : S.card ≤ 1
      · have he : (d+1)*S.card ≤ d+1 := by simpa using Nat.mul_le_mul_left (d+1) small
        have ha : 1 ≤ ((d+1).choose 2+1)*rankOn G S := Nat.mul_pos (by omega) hp
        omega
      by_cases hbig : d*rankOn G S + 1 < S.card
      · obtain ⟨v, hv, hvdeg⟩ := exists_degree_ge_of_inseparable h (d+1) (by simpa using hbig) (by omega)
        have hcard := card_erase_add_one hv
        have hrank := h.rank_erase hv (by omega)
        obtain ⟨P, hu, hd, hi, hs⟩ := exists_rank_partition G (S.erase v)
        have hP : P.Nonempty := by
          by_contra! he
          have : S.erase v = ∅ := by simpa [he] using hu.symm
          rw [this, card_empty] at hcard
          omega
        -- With one part, deleting the vertex pays for the entire step.
        by_cases one : P.card = 1
        · obtain ⟨A, rfl⟩ := card_eq_one.mp one
          have hA : A = S.erase v := by simpa using hu
          subst A
          have hc := ih (S.erase v).card (by omega) G (S.erase v) (hi _ (mem_singleton_self _)) (d+1) rfl
          rw [hrank] at hc
          have hstep := blockEdges_erase_add G S v hv
          have hnstep := congrArg ((d+1) * ·) hcard
          rw [Nat.mul_add, Nat.mul_one] at hnstep
          omega
        -- With several parts, adjoin the deleted vertex to each of them.
        -- The Hall boundary estimate pays for these edges across all parts.
        · have per (A : Finset V) (hA : A ∈ P) :
              (d+1)*(A.card+1) ≤ blockEdges G A + blockerSize G A +
                ((d+1).choose 2+1)*rankOn G A + d := by
            have hAR : A ⊆ S.erase v := (biUnion_subset.mp hu.le) A hA
            have hva : v ∉ A := fun h => notMem_erase v S (hAR h)
            have hlt := strict_part_card hu hd (fun B hB => (hi B hB).nonempty) one A hA
            obtain ⟨K, hKdec, hK, hr, he⟩ := augment_inseparable (hi A hA) v hva
            have hm := card_insert_of_notMem hva
            have hh := ih (insert v A).card (by omega) K (insert v A) hK (d+1) rfl
            simpa only [hm, hr, he, Nat.add_sub_cancel] using hh
          have combined := sum_le_sum per
          have hparts := card_biUnion hd
          simp only [id_eq, hu] at hparts
          simp only [Nat.mul_add, Nat.mul_one, sum_add_distrib, ← mul_sum, sum_const,
            nsmul_eq_mul] at combined
          have hcut := rank_boundary G h hv P hP hu hd hi hs
          rw [hs, hrank] at combined
          rw [← hparts] at combined
          have hnstep := congrArg ((d+1) * ·) hcard
          rw [Nat.mul_add, Nat.mul_one] at hnstep
          simp only [Nat.cast_id] at combined
          omega
      · -- At small order, the inequality for the preceding slope is stronger.
        have hpos : 0 < d := by
          by_contra! he
          have hd : d=0 := by omega
          simp [hd] at hbig
          omega
        have step := lower
        rw [Nat.choose_succ_succ' d 1, Nat.choose_one_right]
        have hc : (d + d.choose 2 + 1)*rankOn G S =
          (d.choose 2+1)*rankOn G S + d*rankOn G S := by ring
        rw [hc, Nat.succ_mul, Nat.add_sub_cancel]
        omega

/-- Summing the bound across disjoint inseparable parts retains the contribution
from the number of parts. -/
theorem rank_partition_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hi : ∀ A ∈ P, RankInseparable G A) (d : ℕ) :
    d*(P.biUnion id).card ≤ blockEdges G (P.biUnion id) +
      (d.choose 2+1)*(∑ A ∈ P, rankOn G A) + (d-1)*P.card := by
  have hs := sum_le_sum fun A hA => rank_density G A (hi A hA) d
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, Nat.cast_id] at hs
  have he := boundary_edge_count G (P.biUnion id) P (Subset.rfl) hd
  rw [card_biUnion hd, Nat.mul_comm (d-1)]
  simp only [id_eq]
  omega

end Erdos617
