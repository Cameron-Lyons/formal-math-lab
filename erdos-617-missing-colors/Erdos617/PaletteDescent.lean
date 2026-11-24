import Erdos617.NestedObstruction
import Erdos617.ForeignTotalBudget

namespace Erdos617

open Finset

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- Within the same minimal obstruction, every other color has its own product
obstruction with the first color. The sum of their second ranks minus one
is strictly less than half of `(r-1)*(t-1)`. -/
theorem MinimalObstruction.exists_palette_product_obstructions (h : MinimalObstruction c k t S)
    (hr : 3 ≤ r) (hb : Balanced c) (htr : t < r) :
    ∃ W : Fin r → Finset V,
      (∀ j ≠ k, W j ⊆ S ∧ RankProductObstruction (colorGraph c k) (colorGraph c j) (W j) ∧
        2 ≤ rankOn (colorGraph c k) (W j) ∧ rankOn (colorGraph c k) (W j) ≤ t ∧
        2 ≤ rankOn (colorGraph c j) (W j)) ∧
      2*(∑ j ∈ univ.erase k, (rankOn (colorGraph c j) (W j)-1)) < (r-1)*(t-1) := by
  classical
  have ht := h.two_le_parameter hr hb htr
  obtain ⟨P,hP,_,budget⟩ := h.exists_foreign_total_rank_budget_strict ht htr hb
  let G := colorGraph c k
  have extract (j : Fin r) : ∃ W : Finset V, j ≠ k → W ⊆ S ∧
      RankProductObstruction G (colorGraph c j) W ∧ 2 ≤ rankOn G W ∧
      rankOn G W ≤ t ∧ 2 ≤ rankOn (colorGraph c j) W ∧
      rankOn (colorGraph c j) W-1 ≤ r-(P j).card := by
    by_cases hj : j=k
    · exact ⟨∅,fun hne => (hne hj).elim⟩
    let H := colorGraph c j
    obtain ⟨hu,hd,hi,hs,hrank⟩ := hP j
    change ∑ A ∈ P j,rankOn H A = rankOn H S at hs
    change rankOn H S ≤ r at hrank
    obtain ⟨A,hA,ha⟩ : ∃ A ∈ P j, t*rankOn H A < A.card := by
      by_contra! small
      have total := sum_le_sum small
      have hc := card_biUnion hd
      simp only [id_eq,hu] at hc
      rw [← hc,←mul_sum,hs,h.card_eq] at total
      have := Nat.mul_le_mul_left t hrank
      omega
    have hAS : A ⊆ S := (biUnion_subset.mp hu.le) A hA
    have hG := (rankOn_mono G hAS).trans_eq (h.rank_eq (by omega))
    obtain ⟨W,hWA,hw⟩ := exists_product_obstruction G H A
      ((Nat.mul_le_mul_right (rankOn H A) hG).trans_lt ha)
    refine ⟨W,fun _ => ⟨hWA.trans hAS,hw,hw.two_le_left (Ne.symm hj),(rankOn_mono G hWA).trans hG,
      hw.symm.two_le_left hj,?_⟩⟩
    have positive := sum_le_sum (s:=(P j).erase A) (f:=fun _ => 1)
      (fun B hB => (hi B (mem_of_mem_erase hB)).rank_pos)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,card_erase_of_mem hA] at positive
    change (P j).card-1 ≤ ∑ B∈(P j).erase A, rankOn H B at positive
    have allParts := sum_erase_add (P j) (rankOn H) hA
    rw [hs] at allParts
    have monotone := rankOn_mono H hWA
    change rankOn H W - 1 ≤ r - (P j).card
    omega
  choose W hW using extract
  refine ⟨W, fun j hj => ?_, ?_⟩
  · obtain ⟨hS,hw,ha,hat,hb,_⟩ := hW j hj
    exact ⟨hS,hw,ha,hat,hb⟩
  let R (j : Fin r) := rankOn (colorGraph c j) (W j)-1
  have per (j : Fin r) (hj : j ∈ univ.erase k) :
      (t-1)*R j ≤ (t-1)*(r-(P j).card) +
        ∑ A ∈ (P j).filter (fun A => rankOn (colorGraph c j) A=1), (t-A.card+1).choose 2 :=
    (Nat.mul_le_mul_left (t-1) (hW j (mem_erase.mp hj).1).2.2.2.2.2).trans (Nat.le_add_right ..)
  have count := sum_le_sum per
  rw [←mul_sum] at count
  have bound := (Nat.mul_le_mul_left 2 count).trans_lt budget
  change 2*(∑ j∈univ.erase k, R j) < (r-1)*(t-1)
  apply Nat.lt_of_mul_lt_mul_left (a:=t-1)
  convert bound using 1 <;> ring

end Erdos617
