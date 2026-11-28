module

public import Erdos617.RankFiveShell
public import Erdos617.MissingMatching

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r t b : ℕ} {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V}

/-- If every missing edge has endpoint weight at least L, a matching in a
set of r+b vertices gives a cost bound for every submatching. -/
theorem missing_matching_endpoint_cost (hr : 2*b+3≤r) (hb : Balanced c) {B : Finset V}
    (sz : B.card=r+b) (no : ∀ U⊆B, ¬(colorGraph c k).IsNClique r U) (w : V → ℕ) {L cost : ℕ}
    (cover : ∀ a∈B, ∀ z∈B, a≠z → ¬(colorGraph c k).Adj a z → L≤w a+w z)
    (budget : ∀ U⊆B, (∑ u∈U,w u)≤cost+U.card.choose 2) :
    ∀ m≤b+1, m*L≤cost+(2*m).choose 2 := by
  classical
  intro m mcap
  obtain ⟨P,pnum,pdis,pinfo⟩ := missing_matching hr hb sz no
  obtain ⟨F,fp,number⟩ := exists_subset_card_eq (s:=P) (mcap.trans_eq pnum.symm)
  have dis : (↑F : Set (Finset V)).PairwiseDisjoint id :=
    fun _ ha _ hc ne => pdis (fp ha) (fp hc) ne
  have pairs (A : Finset V) (hA : A∈F) := pinfo A (fp hA)
  let U := F.biUnion id
  have sub : U⊆B := biUnion_subset.mpr (fun A hA => (pairs A hA).1)
  have two (A : Finset V) (hA : A∈F) : A.card=2 := by
    obtain ⟨_,x,y,ne,rfl,_⟩ := pairs A hA
    exact card_pair ne
  have n : U.card=2*m := by
    rw [show U=F.biUnion id from rfl,card_biUnion dis]
    change (∑ A∈F,A.card)=2*m
    rw [sum_congr rfl two,sum_const,nsmul_eq_mul,Nat.cast_id,number,Nat.mul_comm]
  have pairLow (A : Finset V) (hA : A∈F) : L≤∑ a∈A,w a := by
    obtain ⟨incl,x,y,ne,rfl,absent⟩ := pairs A hA
    rw [sum_pair ne]
    exact cover x (incl (mem_insert_self ..)) y (incl (mem_insert_of_mem (mem_singleton_self _))) ne absent
  have low := sum_le_sum pairLow
  rw [sum_const,nsmul_eq_mul,Nat.cast_id,number] at low
  have up := budget U sub
  rw [n,show U=F.biUnion id from rfl,sum_biUnion dis] at up
  exact low.trans up

/-- A minimum-degree shell controls all feasible matching sizes on the same
residual set, for any lower bound on the joint neighborhoods of nonadjacent pairs. -/
theorem MinimalObstruction.rank_matching_shell (h : MinimalObstruction c k t S)
    (hb : Balanced c) (ht : t<r) {A : Finset V} (sub : A⊆S) (pos : A.Nonempty) :
    let G := colorGraph c k
    ∃ d W cost, W⊂A ∧ W.card+d+1=A.card ∧ rankOn G W+1≤rankOn G A ∧
      blockEdges G A=(d+1).choose 2+cost+blockEdges G W ∧ A.card*d≤2*blockEdges G A ∧
      ∀ b L, d+1=r+b → 2*b+3≤r →
        (∀ D⊆W, rankOn G D+2≤rankOn G A → D.card+L≤W.card) →
        ∀ m≤b+1, m*L≤cost+(2*m).choose 2 := by
  intro G
  obtain ⟨d,W,cost,B,ws,n,rank,eq,avg,ba,sz,data⟩ := rank_shell_account G A pos
  refine ⟨d,W,cost,ws,n,rank,eq,avg,?_⟩
  intro b L db hr lim
  obtain ⟨w,cover,budget⟩ := data L lim
  exact missing_matching_endpoint_cost hr hb (sz.trans db)
    (fun U su => h.no_clique hb ht U (su.trans (ba.trans sub))) w cover budget

end Erdos617
