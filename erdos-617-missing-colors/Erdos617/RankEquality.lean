import Erdos617.RankDensity
import Erdos617.ColorCounts

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

private theorem large_degree_sum {n d E a : ℕ} (hd : 3 ≤ d) (ha : 1 < a)
    (hn : n=d*a+1) (he : d*n=E+(d.choose 2+1)*a+(d-1)) : d*n < 2*E := by
  obtain ⟨h,rfl⟩ : ∃ h, a = h+2 := ⟨a-2, by omega⟩
  obtain ⟨k,rfl⟩ : ∃ k, d = k+3 := ⟨d-3, by omega⟩
  rw [hn] at *
  have hs := congrArg (· * (h+2)) (twice_choose_two (k+3))
  rw [show k+3-1=k+2 by omega] at he
  nlinarith only [he,hs,Nat.zero_le (k*h),Nat.zero_le k,Nat.zero_le h]

theorem rank_one_clique (G : SimpleGraph V) {S : Finset V} (h : rankOn G S = 1) :
    G.IsClique (S : Set V) := by
  intro x hx y hy hxy
  by_contra hn
  have hind : G.IsIndepSet (({x,y} : Finset V) : Set V) := by
    rw [← isClique_compl, coe_insert, coe_singleton, isClique_pair]
    exact fun he => ⟨he,hn⟩
  have hc := card_le_rankOn G (insert_subset hx (singleton_subset_iff.mpr hy)) hind
  simp [h,hxy] at hc

theorem rank_density_order_cap (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h : RankInseparable G S) {d : ℕ} (hd : 1 ≤ d)
    (he : d*S.card = blockEdges G S + (d.choose 2+1)*rankOn G S + (d-1)) :
    S.card ≤ d*rankOn G S+1 := by
  have hn := rank_density G S h (d+1)
  rw [Nat.choose_succ_succ' d 1, Nat.choose_one_right, Nat.succ_mul, Nat.add_sub_cancel] at hn
  have hh : (d+d.choose 2+1)*rankOn G S =
      (d.choose 2+1)*rankOn G S+d*rankOn G S := by ring
  rw [hh] at hn
  omega

private def TwoCliques (G : SimpleGraph V) (S : Finset V) (d : ℕ) : Prop :=
  ∃ C ⊆ S, ∃ D ⊆ S, G.IsNClique d C ∧ G.IsNClique d D ∧ Disjoint C D

private theorem avoiding_of_two {G : SimpleGraph V} {S : Finset V} {d : ℕ}
    (hp : TwoCliques G S d) (z : V) : ∃ C ⊆ S.erase z, G.IsNClique d C := by
  obtain ⟨C,hCS,D,hDS,hC,hD,dis⟩ := hp
  by_cases hz : z ∈ C
  · refine ⟨D, fun w hw => mem_erase.mpr ⟨?_,hDS hw⟩, hD⟩
    rintro rfl
    exact disjoint_left.mp dis hz hw
  · exact ⟨C,fun w hw => mem_erase.mpr ⟨fun eq => hz (eq ▸ hw),hCS hw⟩,hC⟩

/-- On deleting a vertex above the slope from a tight inseparable set, the
augmented rank parts are all tight and have bounded order. -/
theorem tight_augmented_parts (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h : RankInseparable G S) (d : ℕ) (hd : 1 ≤ d)
    (he : d*S.card = blockEdges G S+(d.choose 2+1)*rankOn G S+(d-1)) {v : V}
    (hv : v ∈ S) (big : 1 < S.card) (high : d < (S.filter (G.Adj v)).card)
    (P : Finset (Finset V)) (hu : P.biUnion id = S.erase v)
    (hdis : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hi : ∀ A∈P, RankInseparable G A) (hs : ∑ A∈P, rankOn G A=rankOn G (S.erase v))
    (hP : P.Nonempty) :
    P.card ≠ 1 ∧ (∀ A∈P, d*(A.card+1) =
      blockEdges G A + blockerSize G A + (d.choose 2+1)*rankOn G A + (d-1)) ∧
    ∀ A∈P, A.card ≤ d*rankOn G A := by
  classical
  have hcard := card_erase_add_one hv
  have rankeq := h.rank_erase hv big
  have sizes := card_biUnion hdis
  simp only [id_eq,hu] at sizes
  have multi : P.card ≠ 1 := by
    intro hp
    obtain ⟨A,rfl⟩ := card_eq_one.mp hp
    have hA : A = S.erase v := by simpa using hu
    subst A
    have hlow := rank_density G (S.erase v) (hi _ (mem_singleton_self _)) d
    rw [rankeq] at hlow
    have del := blockEdges_erase_add G S v hv
    have mul := congrArg (d * ·) hcard
    rw [Nat.mul_add, Nat.mul_one] at mul
    omega
  -- Equality of the global bound forces equality on every augmented part.
  let L (A : Finset V) := d*(A.card+1)
  let U (A : Finset V) := blockEdges G A + blockerSize G A + (d.choose 2+1)*rankOn G A + (d-1)
  have sub (A : Finset V) (hA : A ∈ P) : A ⊆ S.erase v := (biUnion_subset.mp hu.le) A hA
  have notin (A : Finset V) (hA : A ∈ P) : v ∉ A := fun hy => notMem_erase v S (sub A hA hy)
  have bound (A : Finset V) (hA : A ∈ P) : L A ≤ U A := by
    obtain ⟨K, _, hK, hr, hedge⟩ := augment_inseparable (hi A hA) v (notin A hA)
    simpa [L, U,card_insert_of_notMem (notin A hA),hr,hedge] using rank_density K (insert v A) hK d
  have tight : ∀ A ∈ P, L A = U A := by
    apply (sum_eq_sum_iff_of_le bound).mp
    apply le_antisymm (sum_le_sum bound)
    simp only [L,U,Nat.mul_add,Nat.mul_one,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id,
      ← sizes, hs, rankeq]
    have hcut := rank_boundary G h hv P hP hu hdis hi hs
    have mul := congrArg (d * ·) hcard
    rw [Nat.mul_add, Nat.mul_one] at mul
    have swap : P.card*(d-1)+P.card=P.card*d := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  have smaller (A : Finset V) (hA : A ∈ P) : A.card ≤ d*rankOn G A := by
    obtain ⟨K, _, hK, hr, hedge⟩ := augment_inseparable (hi A hA) v (notin A hA)
    have hm := card_insert_of_notMem (notin A hA)
    have eq := tight A hA
    have cap := rank_density_order_cap K (insert v A) hK (d := d) (by omega)
      (by simpa only [hm,hr,hedge] using eq)
    rw [hm,hr] at cap
    omega
  exact ⟨multi,tight,smaller⟩

private theorem tight_cliques (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h : RankInseparable G S) (d : ℕ) (hd : 3 ≤ d)
    (hn : S.card = d*rankOn G S+1)
    (he : d*S.card = blockEdges G S+(d.choose 2+1)*rankOn G S+(d-1)) :
    (∀ z, ∃ C ⊆ S.erase z, G.IsNClique d C) ∧ (1 < rankOn G S → TwoCliques G S d) := by
  classical
  induction en : S.card using Nat.strong_induction_on generalizing G S with
  | h n ih =>
    subst n
    by_cases one : rankOn G S = 1
    · refine ⟨fun z => ?_, by omega⟩
      have hS : S.card = d+1 := by simpa [one] using hn
      have hc : d ≤ (S.erase z).card := by rw [card_erase_eq_ite]; split <;> omega
      obtain ⟨C,hC,hcard⟩ := exists_subset_card_eq hc
      exact ⟨C,hC,(rank_one_clique G one).subset (hC.trans (erase_subset ..)),hcard⟩
    have ha : 1 < rankOn G S := by have := h.rank_pos; omega
    have hdeg := large_degree_sum hd ha hn he
    obtain ⟨v, hv, high⟩ : ∃ v ∈ S, d < (S.filter (G.Adj v)).card := by
      by_contra! hu
      have hle := sum_le_sum hu
      rw [block_degree_sum] at hle
      simpa [Nat.mul_comm] using (not_le_of_gt hdeg) (by simpa [Nat.mul_comm] using hle)
    have big : 1 < S.card := by have := Nat.mul_pos (by omega : 0<d) h.rank_pos; omega
    have hcard := card_erase_add_one hv
    have rankeq := h.rank_erase hv big
    obtain ⟨P,hu,hdis,hi,hs⟩ := exists_rank_partition G (S.erase v)
    have sizes := card_biUnion hdis
    simp only [id_eq,hu] at sizes
    have hP : P.Nonempty := by
      by_contra! hp
      have hu0 : S.erase v = ∅ := by simpa [hp] using hu.symm
      rw [hu0, card_empty] at hcard
      omega
    have sub (A : Finset V) (hA : A ∈ P) : A ⊆ S.erase v := (biUnion_subset.mp hu.le) A hA
    have notin (A : Finset V) (hA : A ∈ P) : v ∉ A := fun hy => notMem_erase v S (sub A hA hy)
    obtain ⟨multi,tight,smaller⟩ := tight_augmented_parts G S h d (by omega) he hv big high P hu hdis hi hs hP
    -- The next slope bounds each part, and their orders sum to the common bound.
    have eqsize : ∀ A ∈ P, A.card = d*rankOn G A := by
      apply (sum_eq_sum_iff_of_le smaller).mp
      rw [← sizes, ← mul_sum, hs, rankeq]
      omega
    have partclique (A : Finset V) (hA : A ∈ P) : ∃ C ⊆ A, G.IsNClique d C := by
      obtain ⟨K, _, hK, hr, hedge, same⟩ := augment_inseparable_on (hi A hA) v (notin A hA)
      have hm := card_insert_of_notMem (notin A hA)
      have hlt := strict_part_card hu hdis (fun B hB => (hi B hB).nonempty) multi A hA
      obtain ⟨C,hCA,hC⟩ := (ih (insert v A).card (by omega) K (insert v A) hK
        (by rw [hm,hr,eqsize A hA]) (by simpa only [hm,hr,hedge] using tight A hA) rfl).1 v
      rw [erase_insert (notin A hA)] at hCA
      refine ⟨C,hCA,?_,hC.card_eq⟩
      intro x hx y hy hxy
      exact (same x (hCA hx) y (hCA hy)).mp (hC.isClique hx hy hxy)
    obtain ⟨A,hA,B,hB,hab⟩ := one_lt_card.mp (show 1<P.card by have := card_pos.mpr hP; omega)
    obtain ⟨C,hCA,hC⟩ := partclique A hA
    obtain ⟨D,hDB,hD⟩ := partclique B hB
    have pair : TwoCliques G S d :=
      ⟨C,hCA.trans ((sub A hA).trans (erase_subset ..)),D,hDB.trans ((sub B hB).trans (erase_subset ..)),
        hC,hD,(hdis hA hB hab).mono hCA hDB⟩
    exact ⟨avoiding_of_two pair, fun _ => pair⟩

/-- At the upper order endpoint of a tight linear rank bound, a clique of
order d survives the deletion of any selected vertex. -/
theorem exists_clique_avoiding_of_rank_density_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h : RankInseparable G S) (d : ℕ) (hd : 3 ≤ d)
    (hn : S.card = d*rankOn G S+1)
    (he : d*S.card = blockEdges G S+(d.choose 2+1)*rankOn G S+(d-1)) (z : V) :
    ∃ C ⊆ S.erase z, G.IsNClique d C :=
  (tight_cliques G S h d hd hn he).1 z

/-- A tight inseparable set at the upper endpoint contains a clique of order d. -/
theorem exists_clique_of_rank_density_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h : RankInseparable G S) (d : ℕ) (hd : 3 ≤ d)
    (hn : S.card = d*rankOn G S+1)
    (he : d*S.card = blockEdges G S+(d.choose 2+1)*rankOn G S+(d-1)) :
    ∃ C ⊆ S, G.IsNClique d C := by
  obtain ⟨z, _⟩ := h.nonempty
  obtain ⟨C,hC,hcl⟩ := exists_clique_avoiding_of_rank_density_eq G S h d hd hn he z
  exact ⟨C,hC.trans (erase_subset ..),hcl⟩

/-- For rank at least two, the equality case contains two disjoint cliques of order d. -/
theorem two_disjoint_cliques_of_rank_density_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h : RankInseparable G S) (d : ℕ) (hd : 3 ≤ d)
    (hn : S.card = d*rankOn G S+1)
    (he : d*S.card = blockEdges G S+(d.choose 2+1)*rankOn G S+(d-1))
    (ha : 1 < rankOn G S) :
    ∃ C ⊆ S, ∃ D ⊆ S, G.IsNClique d C ∧ G.IsNClique d D ∧ Disjoint C D :=
  (tight_cliques G S h d hd hn he).2 ha

end Erdos617
