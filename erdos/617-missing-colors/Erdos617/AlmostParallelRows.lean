module

public import Erdos617.ThreeIndependent
public import Erdos617.ParallelRows
public import Erdos617.ParallelTailDegree
public import Erdos617.ParallelFamilyBudget
public import Erdos617.VerifiedRange

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

/-- In any counterexample with r−q disjoint full cliques of one color,
some color has a minimal obstruction of rank at most 2q+1. -/
theorem obstruction_from_parallel_full_cliques {V : Type*} [Fintype V] [DecidableEq V]
    {r m q : ℕ} (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r)
    (hb : Balanced c) (k : Fin r) (mq : m+q=r) (pos : 0<q) (hm : 4≤m)
    (R : Fin m → Finset V) (full : ∀ i,(colorGraph c k).IsNClique r (R i))
    (dis : Pairwise fun i j => Disjoint (R i) (R j)) :
    ∃ (j : Fin r) (t : ℕ) (T : Finset V), t≤2*q+1 ∧ MinimalObstruction c j t T := by
  classical
  by_contra! clear
  let G := colorGraph c k
  let Y := univ.biUnion R
  have count : Y.card=m*r := by
    simp only [Y,card_biUnion (fun _ _ _ _ ne => dis ne),fun i => (full i).card_eq,
      sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  have sz : Yᶜ.card=q*r+1 := by
    have total := card_compl_add_card Y
    rw [hn,count] at total
    nlinarith only [total,congrArg (·*r) mq]
  have high : q<rankOn G Yᶜ := by
    by_contra! low
    have lim := local_rank_cap (c:=c) (k:=k) (s:=2*q+1)
      (fun a ha T => clear k a T ha) Yᶜ (by change rankOn G Yᶜ≤2*q+1; omega)
    change Yᶜ.card≤rankOn G Yᶜ*r at lim
    have product := Nat.mul_le_mul_right r low
    omega
  obtain ⟨I,ii,indI,nI⟩ := exists_max_indep G Yᶜ
  obtain ⟨A,aI,nA⟩ := exists_subset_card_eq (s:=I) (show q+1≤I.card by omega)
  have sub := aI.trans ii
  have ind : G.IsNIndepSet (q+1) A := ⟨indI.mono aI,nA⟩
  have outside (i : Fin m) : Disjoint A (R i) :=
    disjoint_left.mpr fun w hw hy => mem_compl.mp (sub hw) (mem_biUnion.mpr ⟨i,mem_univ _,hy⟩)
  have cross := parallel_family_cross_floor c k hb mq R full dis A ind outside
  have floor := parallel_family_induced_floor G R full dis cross
  have small : blockEdges G Y≤G.edgeFinset.card := by
    rw [←card_inducedEdgeSet]
    apply card_le_card
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b => exact mem_edgeFinset.mpr ((mem_inducedEdgeSet G).mp he).2.2
  exact parallel_family_budget_of_rank_cap hr hn c hb k mq pos hm
    (fun j _ => local_rank_cap (c:=c) (k:=j) (fun a ha T => clear j a T ha))
    (floor.trans (Nat.mul_le_mul_left 2 small))

/-- A coloring that contains r−q disjoint full monochromatic rows in a
single color satisfies the original conjecture whenever 1000(2q+1)²<r.
The choice of colors on all remaining edges is arbitrary. -/
theorem missing_of_almost_parallel_full_cliques {V : Type*} [Fintype V] [DecidableEq V]
    {r m q : ℕ} (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r)
    (k : Fin r) (mq : m+q=r) (large : 1000*(2*q+1)^2<r)
    (R : Fin m → Finset V) (full : ∀ i,(colorGraph c k).IsNClique r (R i))
    (dis : Pairwise fun i j => Disjoint (R i) (R j)) :
    ∃ (S : Finset V) (j : Fin r), S.card=r+1 ∧ ∀ u∈S,∀ v∈S,u≠v → c s(u,v)≠j := by
  classical
  rcases Nat.eq_zero_or_pos q with eq|pos
  · subst q
    simp only [Nat.add_zero] at mq
    subst m
    exact missing_of_parallel_full_cliques hr hn c k R full dis
  by_contra absent
  have hb := balanced_of_no_witness c absent
  have hm : 4≤m := by nlinarith only [large,mq,Nat.zero_le (q*q),pos]
  obtain ⟨j,t,T,bound,obs⟩ := obstruction_from_parallel_full_cliques hr hn c hb k mq pos hm R full dis
  have tr : t<r := by nlinarith only [large,bound,Nat.zero_le (q*q),pos]
  have low := obs.quadratic_bound hr hb tr
  have high := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left bound 2)
  omega

/-- A single color containing r−1 disjoint full cliques suffices at every
palette size in the Erdős–Gyárfás conjecture. -/
theorem missing_of_all_but_one_parallel_row {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (k : Fin r)
    (R : Fin (r-1) → Finset V) (full : ∀ i,(colorGraph c k).IsNClique r (R i))
    (dis : Pairwise fun i j => Disjoint (R i) (R j)) :
    ∃ (S : Finset V) (j : Fin r), S.card=r+1 ∧ ∀ u∈S,∀ v∈S,u≠v → c s(u,v)≠j := by
  by_cases small : r≤10
  · exact missing_of_at_most_ten_colors hr small hn c
  by_contra absent
  have hb := balanced_of_no_witness c absent
  obtain ⟨j,t,T,cap,obs⟩ := obstruction_from_parallel_full_cliques hr hn c hb k
    (q:=1) (by omega) (by decide) (by omega) R full dis
  have floor := obs.five_le_of_nine_le hb (by omega) (by omega)
  omega

/-- If one color contains r−2 disjoint r-cliques, the two missing rows may
have arbitrary edge colors and the conjectured witness still exists. -/
theorem missing_of_all_but_two_parallel_rows {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (k : Fin r)
    (R : Fin (r-2) → Finset V) (full : ∀ i,(colorGraph c k).IsNClique r (R i))
    (dis : Pairwise fun i j => Disjoint (R i) (R j)) :
    ∃ (S : Finset V) (j : Fin r), S.card=r+1 ∧ ∀ u∈S,∀ v∈S,u≠v → c s(u,v)≠j := by
  classical
  by_cases small : r≤10
  · exact missing_of_at_most_ten_colors hr small hn c
  by_contra absent
  have hb := balanced_of_no_witness c absent
  let Y := univ.biUnion R
  let T := Yᶜ
  have sizeY : Y.card=(r-2)*r := by
    simp only [Y,card_biUnion (fun _ _ _ _ ne => dis ne),fun i => (full i).card_eq,
      sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  have sizeT : T.card=2*r+1 := by
    have total := card_compl_add_card Y
    rw [sizeY,hn] at total
    change T.card+_=r^2+1 at total
    nlinarith only [total,congrArg (·*r) (show r-2+2=r by omega)]
  have off (i : Fin (r-2)) : Disjoint T (R i) := disjoint_compl_left.mono_right
    (subset_biUnion_of_mem R (mem_univ i))
  obtain ⟨A,sub,ind⟩ := independent_three_in_subset hr c hb k T sizeT
  have cross := parallel_family_cross_floor c k hb (q:=2) (by omega) R full dis A ind
    (fun i => (off i).mono_left sub)
  have univ_eq : T∪Y=univ := by ext v; simp [T]
  have floor := parallel_rows_with_tail_floor (colorGraph c k) R full dis cross T disjoint_compl_left
    univ_eq (parallel_two_tail_degree (by omega : 11≤r) hb k R full dis T sizeT off)
  rw [sizeT,show r-2-1=r-3 by omega] at floor
  exact parallel_two_tail_budget_impossible (by omega) hn c hb k floor

end Erdos617
