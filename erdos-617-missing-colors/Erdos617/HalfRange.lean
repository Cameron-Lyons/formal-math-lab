module

public import Erdos617.RankDensity
public import Erdos617.ObstructionBounds

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

theorem exists_color_edge_budget (hr : 0 < r) (hV : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) : ∃ k : Fin r, 2*(colorGraph c k).edgeFinset.card ≤ r*(r^2+1) := by
  let E (k : Fin r) := (colorGraph c k).edgeFinset.card
  have hne : (univ : Finset (Fin r)).Nonempty := ⟨⟨0, hr⟩, mem_univ _⟩
  obtain ⟨k, _, hmin⟩ := univ.exists_min_image E hne
  have hs := Finset.sum_le_sum (s := univ) (fun i hi => hmin i hi)
  change ∑ _ : Fin r, E k ≤ ∑ j, (colorGraph c j).edgeFinset.card at hs
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_color_edges, hV] at hs
  refine ⟨k, ?_⟩
  change 2*E k ≤ r*(r^2+1)
  by_contra! hbad
  have hm := Nat.mul_lt_mul_of_pos_left hbad hr
  nlinarith only [hs, hm, twice_choose_two (r^2+1)]

theorem rank_parts_of_edge_budget {e p : ℕ} (hr : 3 ≤ r) (he : 2*e ≤ r*(r^2+1))
    (hd : r*(r^2+1) ≤ e + (r.choose 2+1)*r + (r-1)*p) : r ≤ 2*p := by
  have hpred : r-1+1=r := by omega
  have hc := congrArg (fun n => r*n) (twice_choose_two r)
  have hm : (r-1)*r ≤ (r-1)*(2*p) := by
    nlinarith only [he, hd, hc, congrArg (fun n => n*r) hpred]
  exact Nat.le_of_mul_le_mul_left hm (by omega)

/-- Any balanced coloring at order r²+1 contains a first failed independence bound
on t*r+1 vertices, with t at most the integer part of r/2 plus one. -/
theorem exists_minimalObstruction_half_range (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V),
      1 ≤ t ∧ t ≤ r/2+1 ∧ MinimalObstruction c k t S := by
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
  have hn := rank_partition_density G P hd hi r
  rw [hu, card_univ, hV, blockEdges_univ, hs] at hn
  have hn' := Nat.mul_le_mul_left (r.choose 2+1) hrank
  change 2*G.edgeFinset.card ≤ r*(r^2+1) at hk
  have hp : r ≤ 2*P.card := rank_parts_of_edge_budget hr hk (by omega)
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
  obtain ⟨W, hWA, hW⟩ := exists_subset_card_eq (s := A) (show rankOn G A*r+1 ≤ A.card by omega)
  have hfree : ∀ I ⊆ W, ¬ (colorGraph c k).IsNIndepSet (rankOn G A+1) I := by
    intro I hI hsize
    have hl := card_le_rankOn G (hI.trans hWA) hsize.isIndepSet
    rw [hsize.card_eq] at hl
    omega
  obtain ⟨t, S, ht, _, hm⟩ := minimalObstruction_of_failure hW hfree
  exact ⟨k, t, S, hm.pos, by omega, hm⟩

/-- For r at least seventeen the first obstruction can be chosen with parameter
between five and the integer part of r/2 plus one, inclusive. -/
theorem exists_minimalObstruction_five_to_half (hr : 17 ≤ r) (hV : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k : Fin r) (t : ℕ) (S : Finset V),
      5 ≤ t ∧ t ≤ r/2+1 ∧ MinimalObstruction c k t S := by
  obtain ⟨k, t, S, _, ht, hm⟩ := exists_minimalObstruction_half_range (by omega) hV c hb
  exact ⟨k, t, S, hm.five_le_parameter hr hb (by omega), ht, hm⟩

end Erdos617
