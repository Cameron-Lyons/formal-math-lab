module

public import Erdos617.RankObstruction
public import Erdos617.RankEquality

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
  {S : Finset V}

/-- Every rank-one part in a foreign color is a clique, hence is independent in
the obstruction color and has at most t vertices. -/
theorem MinimalObstruction.foreign_rank_one_cap (h : MinimalObstruction c k t S)
    {j : Fin r} (hjk : j ≠ k) {A : Finset V} (hA : A ⊆ S)
    (hone : rankOn (colorGraph c j) A = 1) : A.card ≤ t := by
  have hc := rank_one_clique _ hone
  have hind : (colorGraph c k).IsIndepSet (A : Set V) := by
    intro x hx y hy hxy he
    exact hjk ((hc hx hy hxy).2.symm.trans he.2)
  by_contra! hn
  obtain ⟨I,hi,hn⟩ := exists_subset_card_eq (s := A) (show t+1 ≤ A.card by omega)
  exact h.free I (hi.trans hA) ⟨hind.mono hi,hn⟩

/-- For rank-one parts the supporting linear bound has an exact triangular
remainder. Summing keeps those remainders in the edge budget. -/
theorem rank_partition_clique_deficits (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : ℕ} (ht : 0 < t) (P : Finset (Finset V))
    (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hi : ∀ A ∈ P, RankInseparable G A)
    (hcap : ∀ A ∈ P, rankOn G A = 1 → A.card ≤ t) :
    t*(P.biUnion id).card +
        (∑ A ∈ P.filter (fun A => rankOn G A = 1), (t-A.card+1).choose 2) ≤
      blockEdges G (P.biUnion id) + (t.choose 2+1)*(∑ A ∈ P,rankOn G A) + (t-1)*P.card := by
  classical
  let D (A : Finset V) := if rankOn G A = 1 then (t-A.card+1).choose 2 else 0
  have per (A : Finset V) (hA : A ∈ P) :
      t*A.card + D A ≤ blockEdges G A + (t.choose 2+1)*rankOn G A + (t-1) := by
    by_cases hrank : rankOn G A = 1
    · have hsize := hcap A hA hrank
      obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hsize
      have hcl := rank_one_clique _ hrank
      have hedge : blockEdges G A = A.card.choose 2 := by
        unfold blockEdges
        have top := (G.induce_eq_top).mpr hcl
        convert SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := A) using 1
        · congr 1
          apply Finset.ext
          intro e
          induction e using Sym2.inductionOn with
          | _ x y =>
            rw [mem_edgeFinset,mem_edgeFinset]
            change (G.induce (A : Set V)).Adj x y ↔ (⊤ : SimpleGraph A).Adj x y
            rw [top]
        · rw [Fintype.card_coe]
      simp only [D,hrank,ite_true,Nat.mul_one,hedge]
      rw [show t-A.card=b by omega]
      have hp := Nat.sub_add_cancel (show 1 ≤ t by omega)
      rw [hb] at hp ⊢
      nlinarith only [twice_choose_two A.card,twice_choose_two (A.card+b),twice_choose_two (b+1),hp]
    · simpa [D,hrank] using rank_density G A (hi A hA) t
  have hs := sum_le_sum per
  simp only [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id] at hs
  have hc := card_biUnion hd
  simp only [id_eq] at hc
  have he := boundary_edge_count G (P.biUnion id) P Subset.rfl hd
  rw [hc,Finset.sum_filter,Nat.mul_comm (t-1)]
  change t*(∑ A ∈ P,A.card) + (∑ A ∈ P,D A) ≤ _
  omega

private theorem foreign_budget_numeric {r t x y p W : ℕ}
    (ht : 2 ≤ t) (htr : t < r) (hp : p ≤ r)
    (hx : r*(t*r+1) ≤ x+(r.choose 2+1)*t+(r-1))
    (hy : x+(r-1)*y ≤ (t*r+1).choose 2)
    (hd : t*(t*r+1)+W ≤ y+(t.choose 2+1)*r+(t-1)*p) :
    2*(r-p)<t-1 ∧ W ≤ t^2 := by
  let d := r-p
  have dp : d+p=r := Nat.sub_add_cancel hp
  obtain ⟨u, hu⟩ : ∃ u, t = u+2 := ⟨t-2,by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, r = t+v+1 := ⟨r-t-1,by omega⟩
  have heft := Nat.mul_le_mul_left (2*(r-1)) hd
  have Ck := congrArg (fun z => t*z) (twice_choose_two r)
  have Ct := congrArg (fun z => (r-1)*r*z) (twice_choose_two t)
  have hD : 2*(r-1)*(t-1)*d + 2*(r-1)*W + 3*r*t+2 ≤ r*t^2+4*t := by
    have m := congrArg (fun z => 2*(r-1)*(t-1)*z) dp
    have mk := congrArg (fun z => z*(t*r+1)) (Nat.sub_add_cancel (show 1≤r by omega))
    have mt := congrArg (fun z => 2*(r-1)*r*z) (Nat.sub_add_cancel (show 1≤t by omega))
    have mr := congrArg (fun z => z*(r*t^2+t)) (Nat.sub_add_cancel (show 1≤r by omega))
    nlinarith only [heft,hx,hy,Ck,Ct,twice_choose_two (t*r+1),m,mk,mt,mr,
      Nat.sub_add_cancel (show 1≤r by omega),Nat.sub_add_cancel (show 1≤t by omega)]
  have hi : r*t^2+4*t < (r-1)*(t-1)*(t-1) + 3*r*t+2 := by
    rw [hv,hu]
    rw [show u+2+v+1-1=u+2+v by omega,show u+2-1=u+1 by omega]
    nlinarith only [Nat.zero_le (u*v),Nat.zero_le (u*u),Nat.zero_le v,Nat.zero_le u]
  have hh : 2*d < t-1 := by
    by_contra! hn
    have hm := Nat.mul_le_mul_left ((r-1)*(t-1)) hn
    nlinarith only [hD,hi,hm,Nat.zero_le ((r-1)*W)]
  refine ⟨hh,?_⟩
  by_contra! hn
  have hm := Nat.mul_le_mul_left (r-1) hn.le
  have sq : r*t^2+4*t < 2*(r-1)*t^2+3*r*t+2 := by
    rw [hv,hu]
    rw [show u+2+v+1-1=u+2+v by omega]
    nlinarith only [Nat.zero_le (u*u*u),Nat.zero_le (v*u*u),Nat.zero_le (u*u),Nat.zero_le (v*u),Nat.zero_le v,Nat.zero_le u]
  nlinarith only [hD,sq,hm,Nat.zero_le ((r-1)*(t-1)*d)]

/-- Every minimal obstruction admits a foreign color with almost r additive
rank parts. Its rank-one parts have bounded total triangular size deficit. -/
theorem MinimalObstruction.exists_foreign_rank_budget (h : MinimalObstruction c k t S)
    (ht : 2 ≤ t) (htr : t < r) (hb : Balanced c) :
    ∃ j : Fin r, j ≠ k ∧ ∃ P : Finset (Finset V), P.biUnion id = S ∧
      (↑P : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ A ∈ P, RankInseparable (colorGraph c j) A) ∧
      (∑ A ∈ P, rankOn (colorGraph c j) A) = rankOn (colorGraph c j) S ∧
      rankOn (colorGraph c j) S ≤ r ∧ 2*(r-P.card)<t-1 ∧
      (∀ A ∈ P, rankOn (colorGraph c j) A = 1 → A.card ≤ t) ∧
      (∑ A ∈ P.filter (fun A => rankOn (colorGraph c j) A = 1), (t-A.card+1).choose 2) ≤ t^2 := by
  classical
  let E (j : Fin r) := blockEdges (colorGraph c j) S
  let F := univ.erase k
  have hcF : F.card = r-1 := by simp [F]
  have hF : F.Nonempty := card_pos.mp (by rw [hcF]; omega)
  obtain ⟨j,hj,hmin⟩ := F.exists_min_image E hF
  have hjk := (mem_erase.mp hj).1
  obtain ⟨P,hu,hd,hi,hs⟩ := exists_rank_partition (colorGraph c j) S
  have rankcap : rankOn (colorGraph c j) S ≤ r := by
    obtain ⟨I,_,hind,hcard⟩ := exists_max_indep (colorGraph c j) S
    by_contra! hlarge
    obtain ⟨J,hJ,hc⟩ := exists_subset_card_eq (s:=I) (show r+1 ≤ I.card by omega)
    obtain ⟨x,hx,y,hy,hxy,he⟩ := hb J hc j
    exact hind (hJ hx) (hJ hy) hxy ⟨hxy,he⟩
  have cap (A : Finset V) (hA : A∈P) := h.foreign_rank_one_cap hjk ((biUnion_subset.mp hu.le) A hA)
  have hi' := rank_partition_clique_deficits _ (by omega : 0<t) P hd hi cap
  rw [hu,h.card_eq,hs] at hi'
  have hle := Nat.mul_le_mul_left (t.choose 2+1) rankcap
  have hp := sum_le_sum (s := P) (f := fun _ => 1) fun A hA => (hi A hA).rank_pos
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,hs] at hp
  have low : F.card*E j ≤ ∑ l ∈ F,E l := by simpa using sum_le_sum hmin
  have total := sum_color_edges (fun e : Sym2 S => c (Sym2.map Subtype.val e))
  simp_rw [←color_blockEdges_eq] at total
  change ∑ l,E l = (Fintype.card S).choose 2 at total
  rw [←sum_erase_add _ _ (mem_univ k),Fintype.card_coe,h.card_eq] at total
  have avg : E k+(r-1)*E j ≤ (t*r+1).choose 2 := by
    rw [←hcF,←total,Nat.add_comm]
    exact Nat.add_le_add_right low _
  have key := h.rank_edge_bound (by omega : 0<r)
  obtain ⟨hparts,hdef⟩ := foreign_budget_numeric ht htr (hp.trans rankcap) key avg
    (hi'.trans (Nat.add_le_add_right (Nat.add_le_add_left hle _) _))
  exact ⟨j,hjk,P,hu,hd,hi,hs,rankcap,hparts,cap,hdef⟩

end Erdos617
