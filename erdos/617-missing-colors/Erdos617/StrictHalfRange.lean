module

public import Erdos617.HalfRange
public import Erdos617.RankEquality

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

theorem matching_budget {r e p : ℕ} (hr : 3 ≤ r) (he : 2*e ≤ r*(r^2+1))
    (hp : 2*p = r) : e + (r.choose 2+1)*r + (r-1)*p ≤ r*(r^2+1) := by
  have hc := congrArg (fun n => r*n) (twice_choose_two r)
  have hm := congrArg (fun n => (r-1)*n) hp
  have hh := congrArg (fun n => n*r) (show r-1+1=r by omega)
  nlinarith only [he, hm, hh, hc]

private theorem tight_order {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (hi : RankInseparable G A) {r : ℕ} (hr : 3 ≤ r)
    (hbig : rankOn G A*r < A.card)
    (htight : r*A.card = blockEdges G A + (r.choose 2+1)*rankOn G A + (r-1)) :
    A.card = r*rankOn G A+1 := by
  have hnext := rank_density G A hi (r+1)
  rw [Nat.choose_succ_succ' r 1, Nat.choose_one_right, Nat.add_sub_cancel] at hnext
  have hpred : r-1+1 = r := by omega
  nlinarith only [hnext, htight, hpred, hbig]

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- A balanced coloring on r²+1 vertices has a first obstruction with parameter
at most the ceiling of r/2, including when r is even. -/
theorem exists_minimalObstruction_ceil_half (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V),
      1 ≤ t ∧ t ≤ (r+1)/2 ∧ MinimalObstruction c k t S := by
  classical
  obtain ⟨k, hk⟩ := exists_color_edge_budget (by omega) hV c
  let G := colorGraph c k
  obtain ⟨P, hu, hd, hi, hs⟩ := exists_rank_partition G univ
  have hrank : rankOn G univ ≤ r := by
    by_contra! hbig
    obtain ⟨I, _, hI, hIr⟩ := exists_max_indep G univ
    obtain ⟨J, hJI, hJ⟩ := exists_subset_card_eq (s := I) (show r+1 ≤ I.card by omega)
    obtain ⟨u, hu, v, hv, huv, hcol⟩ := hb J hJ k
    exact hI (hJI hu) (hJI hv) huv ⟨huv, hcol⟩
  change 2*G.edgeFinset.card ≤ r*(r^2+1) at hk
  have hn := rank_partition_density G P hd hi r
  rw [hu, card_univ, hV, blockEdges_univ, hs] at hn
  have hn' := Nat.mul_le_mul_left (r.choose 2+1) hrank
  have hp := rank_parts_of_edge_budget hr hk (by omega : r*(r^2+1) ≤
    G.edgeFinset.card + (r.choose 2+1)*r + (r-1)*P.card)
  have hcard := card_biUnion hd
  rw [hu, card_univ, hV] at hcard
  simp only [id_eq] at hcard
  obtain ⟨A, hA, hlarge⟩ : ∃ A ∈ P, rankOn G A*r < A.card := by
    by_contra! hall
    have hupp := sum_le_sum hall
    rw [← sum_mul, hs] at hupp
    have := Nat.mul_le_mul_right r hrank
    rw [pow_two] at hcard
    omega
  have hrest : (∑ _ ∈ P.erase A, 1) ≤ ∑ B ∈ P.erase A, rankOn G B :=
    sum_le_sum fun B hB => (hi B (mem_of_mem_erase hB)).rank_pos
  have hsum := sum_erase_add P (rankOn G) hA
  simp only [sum_const, nsmul_eq_mul, Nat.mul_one, card_erase_of_mem hA, Nat.cast_id] at hrest
  rw [hs] at hsum
  suffices hfailure : ∃ a ≤ (r+1)/2, ∃ W : Finset V, W.card = a*r+1 ∧
      ∀ I ⊆ W, ¬ G.IsNIndepSet (a+1) I by
    obtain ⟨a, ha, W, hW, hfree⟩ := hfailure
    obtain ⟨t, S, ht, _, h⟩ := minimalObstruction_of_failure hW hfree
    exact ⟨k, t, S, h.pos, ht.trans ha, h⟩
  by_cases hsmall : rankOn G A ≤ (r+1)/2
  · obtain ⟨W, hWA, hW⟩ := exists_subset_card_eq (s := A) (Nat.succ_le_of_lt hlarge)
    refine ⟨_, hsmall, W, hW, fun I hI hi => ?_⟩
    have hc := card_le_rankOn G (hI.trans hWA) hi.isIndepSet
    rw [hi.card_eq] at hc
    omega
  have hpeq : 2*P.card = r := by omega
  have hmax := matching_budget hr hk hpeq
  have he := boundary_edge_count G univ P hu.le hd
  rw [blockEdges_univ] at he
  have eqA : r*A.card = blockEdges G A + (r.choose 2+1)*rankOn G A + (r-1) := by
    apply le_antisymm (rank_density G A (hi A hA) r)
    by_contra! hlt
    have hstrict := sum_lt_sum (f := fun B : Finset V => r*B.card)
      (g := fun B => blockEdges G B + (r.choose 2+1)*rankOn G B + (r-1))
      (fun B hB => rank_density G B (hi B hB) r) ⟨A, hA, hlt⟩
    simp only [sum_add_distrib, ← mul_sum, ← hcard, hs, sum_const, nsmul_eq_mul,
      Nat.cast_id] at hstrict
    rw [Nat.mul_comm P.card (r-1)] at hstrict
    omega
  have hsize := tight_order G A (hi A hA) hr hlarge eqA
  obtain ⟨C, hCA, hC⟩ := exists_clique_of_rank_density_eq G A (hi A hA) r hr hsize eqA
  let a := rankOn G A - 1
  have ha : a+1 = rankOn G A := by dsimp [a]; omega
  have hW : (A \ C).card = a*r+1 := by
    rw [card_sdiff_of_subset hCA, hsize, hC.card_eq, ← ha, Nat.mul_add, Nat.mul_one,
      Nat.mul_comm r a]
    omega
  refine ⟨a, by omega, A \ C, hW, fun I hI hIcard => ?_⟩
  rw [ha] at hIcard
  have hdisj : Disjoint C I :=
    disjoint_left.mpr fun _ hC' hI' => (mem_sdiff.mp (hI hI')).2 hC'
  obtain ⟨J, hJ, hj⟩ := extend_across_clique_within G C I hC hIcard hdisj (by omega)
    (fun x hx _ hy _ hz => exterior_clique_neighbor_unique c hb k C hC x hx hy hz)
  have hl := card_le_rankOn G (hJ.trans (union_subset hCA (hI.trans sdiff_subset))) hj.isIndepSet
  rw [hj.card_eq] at hl
  omega

theorem exists_minimalObstruction_five_to_ceil_half (hr : 17 ≤ r)
    (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V),
      5 ≤ t ∧ t ≤ (r+1)/2 ∧ MinimalObstruction c k t S := by
  obtain ⟨k, t, S, _, ht, hm⟩ := exists_minimalObstruction_ceil_half (by omega) hV c hb
  exact ⟨k, t, S, hm.five_le_parameter hr hb (by omega), ht, hm⟩

end Erdos617
