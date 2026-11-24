import Erdos617.SparseFullPacking
import Erdos617.PaletteMatching

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r}

/-- Removing any subfamily of the selected rows lowers the independence
bound by its cardinality. -/
theorem FullCliqueRows.subfamily {k : Fin r} {Q P : Finset (Finset V)}
    (h : FullCliqueRows c k Q) (hp : P⊆Q) : FullCliqueRows c k P := by
  classical
  refine ⟨fun _ ha _ hb => h.disjoint (hp ha) (hp hb),fun B hb => h.full B (hp hb),?_⟩
  let G := colorGraph c k
  let R := univ \ Q.biUnion id
  obtain ⟨I,hi,ind,hn⟩ := exists_max_indep G (univ \ P.biUnion id)
  have sub : Q.biUnion id=univ \ R := by ext; simp [R]
  have one (B : Finset V) (hb : B∈Q) :
      (I∩B).card ≤ if B∈P then 0 else 1 := by
    split <;> rename_i hm
    · suffices I∩B=∅ by simp [this]
      exact eq_empty_iff_forall_notMem.mpr (fun x hx => (mem_sdiff.mp (hi (mem_inter.mp hx).1)).2
        (mem_biUnion.mpr ⟨B,hm,(mem_inter.mp hx).2⟩))
    · exact card_le_one.mpr (fun x hx y hy => by
        by_contra ne
        exact ind (mem_inter.mp hx).1 (mem_inter.mp hy).1 ne
          ((h.full B hb).isClique (mem_inter.mp hx).2 (mem_inter.mp hy).2 ne))
  have sum := sum_le_sum one
  have cnt : (∑ B∈Q, if B∈P then 0 else 1)=(Q\P).card := by
    rw [sum_ite]; simp [filter_notMem_eq_sdiff]
  rw [cnt] at sum
  have split := card_inter_complement_sum R I Q sub h.disjoint
  have tail := card_le_rankOn G (inter_subset_right : I∩R ⊆ R) (ind.mono inter_subset_left)
  have left := h.residual
  change rankOn G R+Q.card≤r at left
  have diff := card_sdiff_add_card_eq_card hp
  change rankOn G (univ \ P.biUnion id)+P.card≤r
  omega

/-- Deleting equally many rows of two different colors leaves the exact
square order for a smaller instance, and both selected colors have the
smaller independence bound there. -/
theorem row_square_restriction {i j : Fin r} (ne : i≠j) {P Q : Finset (Finset V)}
    (hp : FullCliqueRows c i P) (hq : FullCliqueRows c j Q) {m : ℕ}
    (cp : P.card=m) (cq : Q.card=m) (hn : Fintype.card V=r^2+1) :
    let U := (univ \ P.biUnion id) ∩ (univ \ Q.biUnion id)
    U.card=(r-m)^2+1 ∧ rankOn (colorGraph c i) U≤r-m ∧ rankOn (colorGraph c j) U≤r-m := by
  classical
  intro U
  let A := univ \ P.biUnion id
  let B := univ \ Q.biUnion id
  have sub : Q.biUnion id=univ \ B := by ext; simp [B]
  have sizes := card_biUnion hp.disjoint
  change (P.biUnion id).card=∑ C∈P,C.card at sizes
  rw [sum_congr rfl (fun C hC => (hp.full C hC).card_eq),sum_const,nsmul_eq_mul,Nat.cast_id,cp] at sizes
  have sum := card_inter_complement_sum B A Q sub hq.disjoint
  have line (K : Finset V) (hK : K∈Q) : (A∩K).card=r-m := by
    have ind : (colorGraph c i).IsNIndepSet r K := ⟨fun _ ha _ hb n e => ne
      (e.2.symm.trans ((hq.full K hK).isClique ha hb n).2),(hq.full K hK).card_eq⟩
    simpa [A,inter_comm,cp] using (hp.transversal ind).1
  rw [sum_congr rfl line,sum_const,nsmul_eq_mul,Nat.cast_id,cq] at sum
  have a := card_sdiff_add_card_eq_card (subset_univ (P.biUnion id))
  change A.card+_=Fintype.card V at a
  rw [sizes,hn] at a
  have left := hp.residual
  have right := hq.residual
  rw [cp] at left
  rw [cq] at right
  have li := rankOn_mono (colorGraph c i) (inter_subset_left : U ⊆ A)
  have lj := rankOn_mono (colorGraph c j) (inter_subset_right : U ⊆ B)
  change rankOn (colorGraph c i) A+m≤r at left
  change rankOn (colorGraph c j) B+m≤r at right
  change rankOn (colorGraph c i) U≤rankOn (colorGraph c i) A at li
  change rankOn (colorGraph c j) U≤rankOn (colorGraph c j) B at lj
  have eq : r-m+m=r := by omega
  refine ⟨?_,by omega,by omega⟩
  change m*(r-m)+U.card=A.card at sum
  nlinarith only [eq,congrArg (·^2) eq,a,sum,congrArg (m*·) eq]

/-- Removing one or two rows of each of two colors leaves a square in
which two distinct original colors already meet the smaller balance test. -/
theorem exists_square_of_at_most_two_rows {m : ℕ} (hm : m≤2) (hr : 5≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-m)^2+1 ∧
      rankOn (colorGraph c i) U≤r-m ∧ rankOn (colorGraph c j) U≤r-m := by
  classical
  obtain ⟨Q,hQ,total,_⟩ := exists_transversal_full_rows hr hn c hb
  let T := univ.filter fun j => 2≤(Q j).card
  have many : 1<T.card := by
    by_contra! few
    have large := sum_le_sum (s:=T) (g:=fun _ => r) fun j _ => Nat.le_of_add_left_le (hQ j).residual
    have small := sum_le_sum (s:=Tᶜ) (g:=fun _ => 1) fun j hj => (by
      have notmem := mem_compl.mp hj
      change j∉univ.filter _ at notmem
      simp only [mem_filter,mem_univ,true_and,not_le] at notmem
      omega : (Q j).card≤1)
    have split := sum_add_sum_compl T (fun j => (Q j).card)
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at large small
    have hcard : Tᶜ.card≤r := by simpa using Tᶜ.card_le_univ
    have bound := Nat.mul_le_mul_right r few
    omega
  obtain ⟨i,hi,j,hj,ne⟩ := one_lt_card.mp many
  obtain ⟨P,hP,cp⟩ := exists_subset_card_eq (s:=Q i) (hm.trans (mem_filter.mp hi).2)
  obtain ⟨R,hR,cr⟩ := exists_subset_card_eq (s:=Q j) (hm.trans (mem_filter.mp hj).2)
  exact ⟨i,j,_,ne,row_square_restriction ne ((hQ i).subfamily hP) ((hQ j).subfamily hR) cp cr hn⟩

/-- Every putative counterexample has a square two colors smaller in
which two distinct original colors already meet the smaller balance test. -/
theorem exists_two_row_square (hr : 5≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-2)^2+1 ∧
      rankOn (colorGraph c i) U≤r-2 ∧ rankOn (colorGraph c j) U≤r-2 :=
  exists_square_of_at_most_two_rows (Nat.le_refl 2) hr hn hb

end Erdos617
