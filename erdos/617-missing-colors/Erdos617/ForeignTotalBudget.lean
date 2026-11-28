module

public import Erdos617.ForeignRankBudget

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- At order t*r+1, both the shortfall in the number of parts and the
triangular deficits of the rank-one cliques are charged to edges above
the ordinary Turán minimum. -/
theorem rank_partition_cost_le_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    {t r : ℕ} (ht : 0 < t) (P : Finset (Finset V))
    (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hi : ∀ A ∈ P, RankInseparable G A) (hn : (P.biUnion id).card = t*r+1)
    (hr : (∑ A ∈ P,rankOn G A) ≤ r) (hcap : ∀ A ∈ P, rankOn G A = 1 → A.card ≤ t) :
    r*t.choose 2 + t + ((t-1)*(r-P.card) +
      ∑ A ∈ P.filter (fun A => rankOn G A = 1), (t-A.card+1).choose 2) ≤
      blockEdges G (P.biUnion id) := by
  have hs := rank_partition_clique_deficits G ht P hd hi hcap
  rw [hn] at hs
  have hp := sum_le_sum (s := P) (f := fun _ => 1) fun A hA => (hi A hA).rank_pos
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at hp
  have dp := congrArg (fun z => (t-1)*z) (Nat.sub_add_cancel (hp.trans hr))
  have tr := congrArg (fun z => z*r) (Nat.sub_add_cancel (show 1≤t by omega))
  have ch := congrArg (fun z => r*z) (twice_choose_two t)
  have hα := Nat.mul_le_mul_left (t.choose 2+1) hr
  nlinarith only [hs,dp,tr,ch,hα]

theorem foreign_total_budget_arithmetic {r t x y T : ℕ} (ht : 2≤t) (htr : t<r)
    (hx : r*(t*r+1) ≤ x+(r.choose 2+1)*t+(r-1))
    (hs : (r-1)*(r*t.choose 2+t)+T ≤ y)
    (hxy : x+y = (t*r+1).choose 2) : 2*T < (r-1)*(t-1)*(t-1) := by
  obtain ⟨u,hu⟩ : ∃ u, t=u+2 := ⟨t-2,by omega⟩
  obtain ⟨v,hv⟩ : ∃ v, r=t+v+1 := ⟨r-t-1,by omega⟩
  have step : r*t^2+4*t < (r-1)*(t-1)*(t-1)+3*r*t+2 := by
    rw [hv,hu,show u+2+v+1-1=u+2+v by omega,show u+2-1=u+1 by omega]
    nlinarith only [Nat.zero_le (u*v),Nat.zero_le (u*u),Nat.zero_le v,Nat.zero_le u]
  have he : 2*T+3*r*t+2 ≤ r*t^2+4*t := by
    have Cr := congrArg (fun z => t*z) (twice_choose_two r)
    have Ct := congrArg (fun z => (r-1)*r*z) (twice_choose_two t)
    have hmul := congrArg (fun z => z*(r*t^2+r*t+t)) (Nat.sub_add_cancel (show 1≤r by omega))
    have hmul' := congrArg (fun z => z*(r*t+t)) (Nat.sub_add_cancel (show 1≤r by omega))
    have hmul'' := congrArg (fun z => z*t) (Nat.sub_add_cancel (show 1≤r by omega))
    nlinarith only [hx,hs,hxy,twice_choose_two (t*r+1),Cr,Ct,hmul,hmul',hmul'',
      Nat.sub_add_cancel (show 1≤r by omega)]
  omega

/-- All foreign colors together have less than the displayed budget for missing
rank parts and for the size deficits of their rank-one cliques. -/
theorem MinimalObstruction.exists_foreign_total_rank_budget_strict {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (ht : 2 ≤ t) (htr : t < r) (hb : Balanced c) :
    ∃ P : Fin r → Finset (Finset V),
      (∀ j, (P j).biUnion id = S ∧ (↑(P j) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ A ∈ P j, RankInseparable (colorGraph c j) A) ∧
        (∑ A ∈ P j,rankOn (colorGraph c j) A) = rankOn (colorGraph c j) S ∧
        rankOn (colorGraph c j) S ≤ r) ∧
      (∀ j, j ≠ k → ∀ A ∈ P j, rankOn (colorGraph c j) A = 1 → A.card ≤ t) ∧
      2*(∑ j ∈ univ.erase k, ((t-1)*(r-(P j).card) +
        ∑ A ∈ (P j).filter (fun A => rankOn (colorGraph c j) A = 1), (t-A.card+1).choose 2)) <
        (r-1)*(t-1)*(t-1) := by
  classical
  choose P hu hd hi hs using fun j : Fin r => exists_rank_partition (colorGraph c j) S
  have rankcap (j : Fin r) : rankOn (colorGraph c j) S ≤ r := by
    obtain ⟨I,_,hind,hcard⟩ := exists_max_indep (colorGraph c j) S
    by_contra! hlarge
    obtain ⟨J,hJ,hc⟩ := exists_subset_card_eq (s:=I) (show r+1 ≤ I.card by omega)
    obtain ⟨x,hx,y,hy,hxy,he⟩ := hb J hc j
    exact hind (hJ hx) (hJ hy) hxy ⟨hxy,he⟩
  have cap (j : Fin r) (hjk : j≠k) (A : Finset V) (hA : A ∈ P j) :=
    h.foreign_rank_one_cap hjk ((biUnion_subset.mp (hu j).le) A hA)
  refine ⟨P,fun j => ⟨hu j,hd j,hi j,hs j,rankcap j⟩,cap,?_⟩
  let T (j : Fin r) := (t-1)*(r-(P j).card) +
    ∑ A ∈ (P j).filter (fun A => rankOn (colorGraph c j) A = 1), (t-A.card+1).choose 2
  let E (j : Fin r) := blockEdges (colorGraph c j) S
  have per (j : Fin r) (hj : j ∈ univ.erase k) : r*t.choose 2+t+T j ≤ E j := by
    have b := rank_partition_cost_le_edges _ (by omega : 0<t) (P j) (hd j) (hi j)
      ((congrArg card (hu j)).trans h.card_eq) ((hs j).le.trans (rankcap j)) (cap j (mem_erase.mp hj).1)
    rwa [hu] at b
  have he := sum_le_sum per
  simp only [sum_add_distrib,sum_const,card_erase_of_mem (mem_univ _),card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at he
  have total := sum_color_edges (fun e : Sym2 S => c (Sym2.map Subtype.val e))
  simp_rw [←color_blockEdges_eq] at total
  change ∑ l,E l = (Fintype.card S).choose 2 at total
  rw [←sum_erase_add _ _ (mem_univ k),Fintype.card_coe,h.card_eq,Nat.add_comm] at total
  rw [← Nat.mul_add] at he
  exact foreign_total_budget_arithmetic ht htr (h.rank_edge_bound (by omega)) he total

/-- A convenient form with one factor t in the total budget. -/
theorem MinimalObstruction.exists_foreign_total_rank_budget {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (ht : 2 ≤ t) (htr : t < r) (hb : Balanced c) :
    ∃ P : Fin r → Finset (Finset V),
      (∀ j, (P j).biUnion id = S ∧ (↑(P j) : Set (Finset V)).PairwiseDisjoint id ∧
        (∀ A ∈ P j, RankInseparable (colorGraph c j) A) ∧
        (∑ A ∈ P j,rankOn (colorGraph c j) A) = rankOn (colorGraph c j) S ∧
        rankOn (colorGraph c j) S ≤ r) ∧
      (∀ j, j ≠ k → ∀ A ∈ P j, rankOn (colorGraph c j) A = 1 → A.card ≤ t) ∧
      2*(∑ j ∈ univ.erase k, ((t-1)*(r-(P j).card) +
        ∑ A ∈ (P j).filter (fun A => rankOn (colorGraph c j) A = 1), (t-A.card+1).choose 2)) <
        (r-1)*t*(t-1) := by
  obtain ⟨P,hP,hcap,hbudget⟩ := h.exists_foreign_total_rank_budget_strict ht htr hb
  refine ⟨P,hP,hcap,hbudget.trans_le ?_⟩
  exact Nat.mul_le_mul_right (t-1) (Nat.mul_le_mul_left (r-1) (Nat.sub_le _ _))

end Erdos617
