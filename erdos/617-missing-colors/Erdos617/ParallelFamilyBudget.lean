module

public import Erdos617.SquareEditDistance
public import Erdos617.QuadraticObstruction
public import Erdos617.DeletionRank

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

private theorem parallel_budget_arithmetic (r m q e : ℕ) (mq : m+q=r) (hq : 0<q)
    (hm : 4≤m)
    (heavy : m*(r*(r-1)+(m-1)*(m-1))≤2*e)
    (all : (r-1)*(r*r.choose 2+r+(r-1)*(2*q+1))+e≤(r^2+1).choose 2) : False := by
  have hr : 1≤r := by omega
  have hm' : 1≤m := by omega
  have edges := twice_choose_two (r^2+1)
  have ch := congrArg (fun n => (r-1)*r*n) (twice_choose_two r)
  zify [hr,hm'] at heavy all edges ch mq
  have excess : 0<(r:ℤ)^2+(3*(q:ℤ)^2-3*q-5)*r-q^3-2*q^2+3*q+2 := by
    obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hq
    zify at hu hv
    rw [←mq,hu,hv]
    ring_nf
    positivity
  have sub : (m:ℤ)=r-q := by omega
  rw [sub] at heavy
  nlinarith only [heavy,all,ch,edges,excess]

/-- A nearly spanning parallel family would make its own color too dense
once every foreign color satisfies its unrestricted local rank bound. -/
theorem parallel_family_budget_of_rank_cap {V : Type*} [Fintype V] [DecidableEq V] {r m q : ℕ}
    (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (k : Fin r) (mq : m+q=r) (hq : 0<q) (hm : 4≤m)
    (rank : ∀ j, j≠k → ∀ A : Finset V, rankOn (colorGraph c j) A≤2*q+1 →
      A.card≤rankOn (colorGraph c j) A*r)
    (heavy : m*(r*(r-1)+(m-1)*(m-1))≤2*(colorGraph c k).edgeFinset.card) : False := by
  classical
  have foreign := sum_le_sum (s:=univ.erase k) fun j hj =>
    full_square_color_edges_of_rank_cap (by omega) hn c hb j (p:=2*q+1) (rank j (mem_erase.mp hj).1)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin] at foreign
  have eq := sum_erase_add univ (fun j => (colorGraph c j).edgeFinset.card) (mem_univ k)
  rw [sum_color_edges,hn] at eq
  exact parallel_budget_arithmetic r m q _ mq hq hm heavy ((Nat.add_le_add_right foreign _).trans_eq eq)

/-- A nearly spanning parallel family would make its own color too dense
once every foreign color satisfies its unrestricted local rank bound. -/
theorem parallel_family_budget_impossible {V : Type*} [Fintype V] [DecidableEq V] {r m q : ℕ}
    (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (k : Fin r) (mq : m+q=r) (hq : 0<q) (large : 1000*(2*q+1)^2<r)
    (heavy : m*(r*(r-1)+(m-1)*(m-1))≤2*(colorGraph c k).edgeFinset.card) : False := by
  classical
  let p := 2*q+1
  have rank (j : Fin r) (A : Finset V) (le : rankOn (colorGraph c j) A≤p) :
      A.card≤rankOn (colorGraph c j) A*r := by
    apply local_rank_cap (s:=p) _ A le
    intro t ht W h
    have qp : q<(2*q+1)^2 := by nlinarith only [Nat.zero_le (q*q),hq]
    have low := h.quadratic_bound hr hb (by dsimp [p] at ht; nlinarith only [large,qp,ht,Nat.zero_le (q^2),hq])
    have up := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left ht 2)
    change 1000*t^2≤1000*(2*q+1)^2 at up
    omega
  have mh : 4≤m := by nlinarith only [mq,large,hq,Nat.zero_le (q^2)]
  exact parallel_family_budget_of_rank_cap hr hn c hb k mq hq mh (fun j _ => rank j) heavy

/-- With two rows missing, the edges incident to the remaining 2r+1
vertices make the rank-four edge floors in the other colors sufficient. -/
theorem parallel_two_tail_budget_impossible {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 11≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (k : Fin r) (heavy : (r-2)*(r*(r-1)+(r-3)*(r-3))+r*(2*r+1)≤2*(colorGraph c k).edgeFinset.card) :
    False := by
  classical
  have rank (j : Fin r) (A : Finset V) (le : rankOn (colorGraph c j) A≤4) :
      A.card≤rankOn (colorGraph c j) A*r :=
    local_rank_cap (s:=4) (fun t ht W h => by
      have := h.five_le_of_nine_le hb (by omega) (by omega)
      omega) A le
  have foreign := sum_le_sum (s:=univ.erase k) fun j _ =>
    full_square_color_edges_of_rank_cap (by omega) hn c hb j (p:=4) (rank j)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,card_erase_of_mem (mem_univ k),card_univ,Fintype.card_fin] at foreign
  have eq := sum_erase_add univ (fun j => (colorGraph c j).edgeFinset.card) (mem_univ k)
  rw [sum_color_edges,hn] at eq
  have all := (Nat.add_le_add_right foreign _).trans_eq eq
  have edges := twice_choose_two (r^2+1)
  have col := congrArg (fun n => (r-1)*r*n) (twice_choose_two r)
  zify [show 1≤r by omega,show 2≤r by omega,show 3≤r by omega] at heavy all col edges
  nlinarith only [heavy,all,col,edges,show (11:ℤ)≤r by omega,sq_nonneg (r:ℤ)]

end Erdos617
