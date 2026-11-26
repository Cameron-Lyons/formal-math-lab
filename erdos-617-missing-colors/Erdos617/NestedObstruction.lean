module

public import Erdos617.RankIntersection
public import Erdos617.ForeignRankBudget
public import Erdos617.QuadraticObstruction

@[expose] public section

namespace Erdos617

open Finset

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- Every first obstruction contains a two-color obstruction. The rank of the
second color there is at most half of t. -/
theorem MinimalObstruction.exists_nested_product_obstruction (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (htr : t < r) :
    ∃ j : Fin r, j ≠ k ∧ ∃ W ⊆ S,
      RankProductObstruction (colorGraph c k) (colorGraph c j) W ∧
      rankOn (colorGraph c k) W ≤ t ∧ 2*rankOn (colorGraph c j) W ≤ t ∧
      2 ≤ rankOn (colorGraph c k) W ∧ 2 ≤ rankOn (colorGraph c j) W ∧
      2*W.card ≤ t^2+2 := by
  classical
  obtain ⟨j,hjk,P,hu,hd,hi,hs,hrank,hp,_,_⟩ :=
    h.exists_foreign_rank_budget (h.two_le_parameter hr hb htr) htr hb
  let G := colorGraph c k
  let H := colorGraph c j
  change (∑ A ∈ P, rankOn H A) = rankOn H S at hs
  change rankOn H S ≤ r at hrank
  obtain ⟨A,hA,hbig⟩ : ∃ A ∈ P, t*rankOn H A < A.card := by
    by_contra! hsmall
    have lower := sum_le_sum hsmall
    have hc := card_biUnion hd
    simp only [id_eq,hu] at hc
    rw [← hc,← mul_sum,hs,h.card_eq] at lower
    have := Nat.mul_le_mul_left t hrank
    omega
  have hAS : A ⊆ S := (biUnion_subset.mp hu.le) A hA
  have amax := sum_le_sum (s := P.erase A) (f := fun _ => 1)
    fun B hB => (hi B (mem_of_mem_erase hB)).rank_pos
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_erase_of_mem hA] at amax
  change P.card-1 ≤ ∑ B ∈ P.erase A, rankOn H B at amax
  have ha := sum_erase_add P (rankOn H) hA
  rw [hs] at ha
  have hhalf : 2*rankOn H A ≤ t := by omega
  have hG : rankOn G A ≤ t := (rankOn_mono G hAS).trans_eq (h.rank_eq (by omega))
  have hov := (Nat.mul_le_mul_right (rankOn H A) hG).trans_lt hbig
  obtain ⟨W,hWA,hW⟩ := exists_product_obstruction G H A hov
  have hfirst := (rankOn_mono G hWA).trans hG
  have hsecond := (Nat.mul_le_mul_left 2 (rankOn_mono H hWA)).trans hhalf
  refine ⟨j,hjk,W,hWA.trans hAS,hW,hfirst,hsecond,hW.two_le_left hjk.symm,hW.symm.two_le_left hjk,?_⟩
  have hm := Nat.mul_le_mul hfirst hsecond
  rw [hW.card_eq]
  nlinarith only [hm]

/-- The outer obstruction and its nested two-color obstruction satisfy their
respective independence bounds on the same coloring. -/
theorem exists_nested_obstruction_quadratic_range [Fintype V] (hr : 3 ≤ r)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (k j : Fin r) (t : ℕ) (S W : Finset V), j ≠ k ∧ W ⊆ S ∧
      r ≤ 1000*t^2 ∧ t ≤ (r+1)/2 ∧ MinimalObstruction c k t S ∧
      RankProductObstruction (colorGraph c k) (colorGraph c j) W ∧
      rankOn (colorGraph c k) W ≤ t ∧ 2*rankOn (colorGraph c j) W ≤ t ∧
      2 ≤ rankOn (colorGraph c k) W ∧ 2 ≤ rankOn (colorGraph c j) W ∧
      2*W.card ≤ t^2+2 := by
  obtain ⟨k,t,S,hlo,hhi,h⟩ := exists_minimalObstruction_quadratic_range hr hn c hb
  obtain ⟨j,hjk,W,hWS,hw⟩ := h.exists_nested_product_obstruction hr hb (by omega)
  exact ⟨k,j,t,S,W,hjk,hWS,hlo,hhi,h,hw⟩

end Erdos617
