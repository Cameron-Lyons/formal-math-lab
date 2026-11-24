import Erdos617.ColorCounts
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Erdos617

open Finset SimpleGraph

private theorem two_remainder_turan {r : ℕ} (hr : 3≤r) (m : ℕ) :
    (m*r+2).choose 2 = turanNumber (m*r+2) r+r*m.choose 2+2*m := by
  have chooseAdd (a b : ℕ) : (a+b).choose 2=a.choose 2+a*b+b.choose 2 := by
    nlinarith only [twice_choose_two a,twice_choose_two b,twice_choose_two (a+b)]
  have pred : r-1+1=r := by omega
  induction m with
  | zero =>
    have top : turanGraph 2 r=⊤ := turanGraph_eq_top.mpr (Or.inr (by omega))
    have base : turanNumber 2 r=1 := by
      unfold turanNumber
      have eg : (turanGraph 2 r).edgeFinset=(⊤ : SimpleGraph (Fin 2)).edgeFinset := by
        ext e; rw [mem_edgeFinset,mem_edgeFinset,top]
      rw [eg,card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin]; decide
    norm_num [base,Nat.choose]
  | succ m ih =>
    rw [Nat.succ_mul, Nat.add_right_comm _ r 2, turanNumber_add, chooseAdd,
      Nat.choose_succ_succ' m 1,Nat.choose_one_right,ih]
    nlinarith only [congrArg ((m*r+2)*·) pred]

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}

private theorem square_comp_edges (hr : 3≤r) (hn : Fintype.card V=(r-1)^2+1) :
    G.edgeFinset.card+Gᶜ.edgeFinset.card=turanNumber (Fintype.card V) r+r*(r-2).choose 2+2*(r-2) := by
  have dis : Disjoint G.edgeFinset Gᶜ.edgeFinset := disjoint_edgeFinset.mpr disjoint_compl_right
  have all : G.edgeFinset ∪ Gᶜ.edgeFinset=(⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      by_cases adj : G.Adj u v
      · simp [mem_union,mem_edgeFinset,adj,adj.ne]
      · simp [mem_union,mem_edgeFinset,adj]
  have size : Fintype.card V=(r-2)*r+2 := by
    rw [hn]; obtain ⟨a,eq⟩ := Nat.exists_eq_add_of_le hr
    rw [eq,show 3+a-1=a+2 by omega,show 3+a-2=a+1 by omega]; ring
  rw [←card_union_of_disjoint dis,all,card_edgeFinset_top_eq_card_choose_two,size]
  exact two_remainder_turan hr _

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem square_comp_free (cap : G.indepNum≤r) : Gᶜ.CliqueFree (r+1) := by
  intro C cl
  have ind := G.isNClique_compl.mp cl
  have bound := ind.isIndepSet.card_le_indepNum.trans cap
  rw [ind.card_eq] at bound
  omega

/-- The edge floor when a graph on (r−1)²+1 vertices has independence number at most r. -/
theorem square_turan_floor (hr : 3≤r) (hn : Fintype.card V=(r-1)^2+1) (cap : G.indepNum≤r) :
    r*(r-2).choose 2+2*(r-2)≤G.edgeFinset.card := by
  have upper := (square_comp_free G cap).card_edgeFinset_le
  have all := square_comp_edges G hr hn
  omega

/-- At the edge floor the graph is the disjoint union of r cliques; each has
order r−2 or r−1. -/
theorem square_turan_rigid (hr : 3≤r) (hn : Fintype.card V=(r-1)^2+1) (cap : G.indepNum≤r)
    (tight : G.edgeFinset.card=r*(r-2).choose 2+2*(r-2)) :
    ∃ P : Fin r → Finset V, univ.biUnion P=univ ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (∀ i, G.IsClique (P i : Set V) ∧ ((P i).card=r-2 ∨ (P i).card=r-1)) ∧
      (∀ i j, i≠j → ∀ x∈P i, ∀ y∈P j, ¬G.Adj x y) := by
  classical
  have upper : Gᶜ.edgeFinset.card=turanNumber (Fintype.card V) r := by
    have all := square_comp_edges G hr hn
    omega
  have max : Gᶜ.IsTuranMaximal r := ⟨square_comp_free G cap,fun H _ cf => cf.card_edgeFinset_le.trans_eq upper.symm⟩
  let F := max.finpartition
  have size : Fintype.card V=(r-2)*r+2 := by
    rw [hn]; obtain ⟨a,eq⟩ := Nat.exists_eq_add_of_le hr
    rw [eq,show 3+a-1=a+2 by omega,show 3+a-2=a+1 by omega]; ring
  have partN : F.parts.card=r := max.card_parts.trans (min_eq_right (by
    rw [size]; exact (Nat.le_mul_of_pos_left _ (by omega : 0<r-2)).trans (Nat.le_add_right ..)))
  let idx : Fin r ≃ F.parts := (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans partN)).symm
  let P (i : Fin r) := (idx i).val
  have mem (i : Fin r) : P i∈F.parts := (idx i).prop
  have part (i : Fin r) {x : V} (hx : x∈P i) : F.part x=P i := F.part_eq_of_mem (mem i) hx
  have diff {i j : Fin r} (ne : i≠j) : P i≠P j := fun eq => ne (idx.injective (Subtype.ext eq))
  have avg : Fintype.card V/r=r-2 := by
    rw [size,Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0<r),Nat.div_eq_of_lt (by omega : 2<r),Nat.zero_add]
  refine ⟨P,eq_univ_of_forall (fun x => ?_),fun i j ne => F.disjoint (mem i) (mem j) (diff ne),?_,?_⟩
  · let C : F.parts := ⟨F.part x,F.part_mem.mpr (mem_univ _)⟩
    exact mem_biUnion.mpr ⟨idx.symm C,mem_univ _,by change x∈(idx (idx.symm C)).val; rw [idx.apply_symm_apply]; exact F.mem_part (mem_univ _)⟩
  · intro i
    refine ⟨?_,?_⟩
    · intro x hx y hy ne
      have n := max.not_adj_iff_part_eq.mpr ((part i hx).trans (part i hy).symm)
      by_contra nodge
      exact n ⟨ne,nodge⟩
    · have sizes := max.isEquipartition.card_parts_eq_average (mem i)
      change (P i).card=univ.card/F.parts.card ∨ (P i).card=univ.card/F.parts.card+1 at sizes
      rw [card_univ,partN,avg] at sizes
      omega
  · intro i j ne x hx y hy e
    have equal := max.not_adj_iff_part_eq.mp (fun bad => bad.2 e)
    exact diff ne ((part i hx).symm.trans (equal.trans (part j hy)))

end Erdos617
