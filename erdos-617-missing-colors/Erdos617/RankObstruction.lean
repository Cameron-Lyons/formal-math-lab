module

public import Erdos617.RankDensity
public import Erdos617.ObstructionBounds

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

omit [DecidableEq V] in
private theorem MinimalObstruction.card_le_rank_mul (h : MinimalObstruction c k t S)
    (hr : 0 < r) {A : Finset V} (hA : A ⊂ S) :
    A.card ≤ rankOn (colorGraph c k) A * r := by
  obtain ⟨I, hIA, hI, hc⟩ := h.proper_subset hr A hA
  exact hc.trans (Nat.mul_le_mul_right _ (card_le_rankOn _ hIA hI))

theorem MinimalObstruction.rank_eq (h : MinimalObstruction c k t S) (hr : 0 < r) :
    rankOn (colorGraph c k) S = t := by
  apply le_antisymm
  · by_contra! hsmall
    obtain ⟨I, hIS, hi, hcard⟩ := exists_max_indep (colorGraph c k) S
    obtain ⟨J, hJI, hJ⟩ := exists_subset_card_eq (s := I) (n := t+1) (by omega)
    exact h.free J (hJI.trans hIS) ⟨hi.mono hJI, hJ⟩
  · obtain ⟨v, hv⟩ := card_pos.mp (show 0 < S.card by rw [h.card_eq]; omega)
    have hc := h.card_le_rank_mul hr (erase_ssubset hv)
    rw [card_erase_of_mem hv, h.card_eq, Nat.add_sub_cancel] at hc
    exact (Nat.le_of_mul_le_mul_right hc hr).trans (rankOn_mono _ (erase_subset ..))

/-- Every nontrivial partition of a minimal obstruction raises the sum of the
two independence numbers. -/
theorem MinimalObstruction.rank_inseparable (h : MinimalObstruction c k t S) (hr : 0 < r) :
    RankInseparable (colorGraph c k) S := by
  refine ⟨card_pos.mp (by rw [h.card_eq]; omega), ?_⟩
  intro A B ha hb hd hu
  have hA : A ⊂ S := by
    rw [← hu]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, ?_⟩
    obtain ⟨b, hb⟩ := hb
    exact fun he => disjoint_left.mp hd (he ▸ mem_union_right A hb) hb
  have hB : B ⊂ S := by
    rw [← hu]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_right, ?_⟩
    obtain ⟨a, ha⟩ := ha
    exact fun he => disjoint_left.mp hd ha (he ▸ mem_union_left B ha)
  have hc := Nat.add_le_add (h.card_le_rank_mul hr hA) (h.card_le_rank_mul hr hB)
  rw [← card_union_of_disjoint hd, hu, h.card_eq, ← Nat.add_mul] at hc
  rw [h.rank_eq hr]
  exact Nat.lt_of_mul_lt_mul_right hc

theorem color_blockEdges_eq (S : Finset V) (c : Sym2 V → Fin r) (k : Fin r) :
    blockEdges (colorGraph c k) S =
      (colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k).edgeFinset.card := by
  unfold blockEdges
  apply congrArg Finset.card
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    constructor
    · intro h
      have e := mem_edgeFinset.mp h
      exact mem_edgeFinset.mpr ⟨fun he => e.1 (congrArg Subtype.val he), e.2⟩
    · intro h
      have e := mem_edgeFinset.mp h
      exact mem_edgeFinset.mpr ⟨fun he => e.1 (Subtype.ext he), e.2⟩

/-- The target color of an obstruction satisfies the bound for a single
rank-inseparable part. -/
theorem MinimalObstruction.rank_edge_bound (h : MinimalObstruction c k t S) (hr : 0 < r) :
    r*(t*r+1) ≤ blockEdges (colorGraph c k) S + (r.choose 2+1)*t + (r-1) := by
  simpa [h.card_eq, h.rank_eq hr] using rank_density _ S (h.rank_inseparable hr) r

private theorem rank_obstruction_arithmetic (r t x y : ℕ) (hr : 0 < r) (ht : 2 ≤ t)
    (hx : r*(t*r+1) ≤ x+(r.choose 2+1)*t+(r-1))
    (hy : (r-1)*(r*t.choose 2+2*t-1) ≤ y)
    (hxy : y+x = (t*r+1).choose 2) :
    5*r*t+4 ≤ r*t^2+2*r+6*t := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m+1 := ⟨r-1, by omega⟩
  simp only [Nat.add_sub_cancel] at hx hy
  let L := (m+1)*t.choose 2+2*t-1
  have hL : L+1 = (m+1)*t.choose 2+2*t := by dsimp [L]; omega
  change m*L ≤ y at hy
  have hM := congrArg (m * ·) hL
  have hC := congrArg (fun z => m*(m+1)*z) (twice_choose_two t)
  have hR := congrArg (fun z => t*z) (twice_choose_two (m+1))
  nlinarith only [hx, hy, hxy, hM, hC, hR, twice_choose_two (t*(m+1)+1)]

/-- Counting all colors in a minimal obstruction bounds its parameter uniformly. -/
theorem MinimalObstruction.rank_parameter_bound (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (ht : t < r) :
    5*r*t+4 ≤ r*t^2+2*r+6*t := by
  let cp : Sym2 S → Fin r := fun e => c (Sym2.map Subtype.val e)
  let E (j : Fin r) := (colorGraph cp j).edgeFinset.card
  have htwo := h.two_le_parameter hr hb ht
  have hx := h.rank_edge_bound (by omega : 0 < r)
  rw [color_blockEdges_eq] at hx
  have hy := h.foreign_edge_sum hb htwo
  have htotal := sum_color_edges cp
  change ∑ j, E j = (Fintype.card S).choose 2 at htotal
  rw [← sum_erase_add _ _ (mem_univ k), Fintype.card_coe, h.card_eq] at htotal
  exact rank_obstruction_arithmetic r t _ _ (by omega) htwo hx hy htotal

/-- With at least eleven colors the first failure has parameter at least five. -/
theorem MinimalObstruction.five_le_of_eleven_le (h : MinimalObstruction c k t S)
    (hr : 11 ≤ r) (hb : Balanced c) (ht : t < r) : 5 ≤ t := by
  have htwo := h.two_le_parameter (by omega) hb ht
  have hbound := h.rank_parameter_bound (by omega) hb ht
  by_contra! hsmall
  have hc : t = 2 ∨ t = 3 ∨ t = 4 := by omega
  rcases hc with rfl | rfl | rfl <;> norm_num at hbound <;> omega

end Erdos617
