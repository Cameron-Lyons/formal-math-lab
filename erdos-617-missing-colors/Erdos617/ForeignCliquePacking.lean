module

public import Erdos617.ForeignTotalBudget
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

/-- Count the large rank-one parts. A part of larger rank consumes at least
one extra unit of rank. A short clique consumes a triangular size deficit. -/
private theorem count_large_rank_one {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) {r t d : ℕ}
    (hcost : t-1 ≤ 2*(d+2).choose 2)
    (hpos : ∀ A ∈ P, 1 ≤ rankOn G A) (hrank : (∑ A ∈ P, rankOn G A) ≤ r) :
    let L := P.filter fun A => rankOn G A=1 ∧ t≤A.card+d
    (t-1)*(r-L.card) ≤ 2*((t-1)*(r-P.card) +
      ∑ A ∈ P.filter (fun A => rankOn G A=1), (t-A.card+1).choose 2) := by
  classical
  intro L
  let Q := P.filter fun A => rankOn G A=1
  have hQP : Q ⊆ P := filter_subset ..
  have hLQ : L ⊆ Q := by
    intro A hA
    exact mem_filter.mpr ⟨(mem_filter.mp hA).1, (mem_filter.mp hA).2.1⟩
  have hLP : L ⊆ P := hLQ.trans hQP
  have hp : P.card ≤ r := by
    have hsum := sum_le_sum (s := P) hpos
    exact (by simpa using hsum : P.card ≤ ∑ A∈P,rankOn G A).trans hrank
  have hhigh (A : Finset V) (hA : A ∈ P \ Q) : 2 ≤ rankOn G A := by
    obtain ⟨ha,hq⟩ := mem_sdiff.mp hA
    have hne : rankOn G A ≠ 1 := fun he => hq (mem_filter.mpr ⟨ha,he⟩)
    have := hpos A ha
    omega
  have hits := sum_le_sum (s := P \ Q) hhigh
  have qrank : (∑ A ∈ Q, rankOn G A) = Q.card := by
    calc
      _ = ∑ _ ∈ Q, 1 := sum_congr rfl fun _ ha => (mem_filter.mp ha).2
      _ = _ := by simp
  have partition := sum_sdiff hQP (f := rankOn G)
  rw [qrank] at partition
  have tall : (P \ Q).card ≤ r-P.card := by
    have hpc := card_sdiff_add_card_eq_card hQP
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at hits
    omega
  let gap (A : Finset V) := (t-A.card+1).choose 2
  have short (A : Finset V) (ha : A ∈ Q \ L) : t-1 ≤ 2*gap A := by
    obtain ⟨hq,hl⟩ := mem_sdiff.mp ha
    obtain ⟨hp, hrone⟩ := mem_filter.mp hq
    have hsmall : A.card+d<t := lt_of_not_ge fun hle => hl (mem_filter.mpr ⟨hp,hrone,hle⟩)
    exact hcost.trans (Nat.mul_le_mul_left 2 (Nat.choose_le_choose 2 (by omega : d+2 ≤ t-A.card+1)))
  have sh := sum_le_sum (s := Q \ L) short
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,← mul_sum] at sh
  have sh' := Nat.mul_le_mul_left 2 (sum_le_sum_of_subset (sdiff_subset : Q \ L ⊆ Q) (f := gap))
  have cards : r-L.card = (r-P.card)+(P \ Q).card+(Q \ L).card := by
    have := card_sdiff_add_card_eq_card hQP
    have := card_sdiff_add_card_eq_card hLQ
    omega
  rw [cards]
  change _ ≤ 2*((t-1)*(r-P.card)+∑ A∈Q, gap A)
  nlinarith only [sh, sh', Nat.mul_le_mul_left (t-1) tall]

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- Inside every minimal obstruction, the other colors contain, in total,
more than (r−1)(r−t+1) cliques of size at least t−⌊√t⌋, disjoint within each
color. Families live on the same vertex set S. -/
theorem MinimalObstruction.foreign_clique_packing (h : MinimalObstruction c k t S)
    (ht : 2 ≤ t) (htr : t < r) (hb : Balanced c) :
    ∃ C : Fin r → Finset (Finset V),
      (∀ j ≠ k, (↑(C j) : Set (Finset V)).PairwiseDisjoint id ∧
        ∀ A ∈ C j, A ⊆ S ∧ (colorGraph c j).IsClique (A : Set V) ∧
          A.card ≤ t ∧ t ≤ A.card+Nat.sqrt t) ∧
      (r-1)*(r-(t-1)) < ∑ j ∈ univ.erase k, (C j).card := by
  classical
  obtain ⟨P, hP, hcap, htotal⟩ := h.exists_foreign_total_rank_budget_strict ht htr hb
  let C (j : Fin r) := (P j).filter fun A => rankOn (colorGraph c j) A=1 ∧ t ≤ A.card+Nat.sqrt t
  let F := univ.erase k
  let cost (j : Fin r) := (t-1)*(r-(P j).card) +
    ∑ A ∈ (P j).filter (fun A => rankOn (colorGraph c j) A=1), (t-A.card+1).choose 2
  refine ⟨C, ?_, ?_⟩
  · intro j hj
    obtain ⟨hu, hd, _, _, _⟩ := hP j
    refine ⟨fun _ ha _ hz he => hd (mem_filter.mp ha).1 (mem_filter.mp hz).1 he, ?_⟩
    intro A hA
    obtain ⟨hp, hr, hs⟩ := mem_filter.mp hA
    exact ⟨biUnion_subset.mp hu.le A hp,rank_one_clique _ hr,hcap j hj A hp hr,hs⟩
  have sqrtcost : t-1 ≤ 2*(Nat.sqrt t+2).choose 2 := by
    have ha := Nat.lt_succ_sqrt' t
    have hc := twice_choose_two (Nat.sqrt t+2)
    nlinarith only [ha,hc,Nat.zero_le (Nat.sqrt t),Nat.sub_le t 1]
  have part (j : Fin r) (_ : j ∈ F) : (t-1)*(r-(C j).card) ≤ 2*cost j := by
    obtain ⟨_, _, hi,hs,hlim⟩ := hP j
    apply count_large_rank_one _ _ sqrtcost (fun A ha => (hi A ha).rank_pos)
    exact hs.trans_le hlim
  have hcnt := sum_le_sum part
  simp only [← mul_sum] at hcnt
  change 2*(∑ j∈F, cost j)<(r-1)*(t-1)*(t-1) at htotal
  have count : (∑ j∈F, (r-(C j).card)) < (r-1)*(t-1) := by
    have tmp := lt_of_le_of_lt hcnt htotal
    rw [Nat.mul_comm ((r-1)*(t-1))] at tmp
    exact Nat.lt_of_mul_lt_mul_left tmp
  have per (j : Fin r) (_ : j ∈ F) : r ≤ (r-(C j).card)+(C j).card := by omega
  have counted := sum_le_sum per
  simp only [sum_add_distrib, sum_const,nsmul_eq_mul,Nat.cast_id] at counted
  have fc : F.card=r-1 := by simp [F]
  have eq := congrArg (fun v => (r-1)*v) (Nat.sub_add_cancel (show t-1 ≤ r by omega))
  change _ < ∑ j∈F,(C j).card
  rw [fc] at counted
  rw [Nat.mul_add] at eq
  omega

end Erdos617
