import Erdos617.RankOneFamilies
import Erdos617.GlobalCliqueEnergy

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} {c : Sym2 V → Fin r}

/-- Removing m monochromatic clique rows from each of two colors leaves at
least (r−m)²+1 vertices when each removal lowers that color's rank by m.
Short rows are allowed, so the remaining set can be trimmed to exact size. -/
theorem exists_square_of_clique_rows (hn : Fintype.card V=r^2+1) (hb : Balanced c)
    {i j : Fin r} (ne : i≠j) {m : ℕ} (hm : m≤r) (P Q : Finset (Finset V))
    (cp : P.card=m) (cq : Q.card=m)
    (clP : ∀ C∈P,(colorGraph c i).IsClique (C : Set V))
    (clQ : ∀ C∈Q,(colorGraph c j).IsClique (C : Set V))
    (ri : rankOn (colorGraph c i) (univ \ P.biUnion id)≤r-m)
    (rj : rankOn (colorGraph c j) (univ \ Q.biUnion id)≤r-m) :
    ∃ U : Finset V, U.card=(r-m)^2+1 ∧ rankOn (colorGraph c i) U≤r-m ∧
      rankOn (colorGraph c j) U≤r-m := by
  classical
  let A := univ \ Q.biUnion id
  let R := A \ P.biUnion id
  have sizeQ (C : Finset V) (hC : C∈Q) : C.card≤r := by
    have ind : (colorGraph c i).IsIndepSet (C : Set V) :=
      fun _ hx _ hy hxy e => ne (e.2.symm.trans (clQ C hC hx hy hxy).2)
    exact ind.card_le_indepNum.trans (balanced_indepNum_le _ hb i)
  have sizeP (C : Finset V) (hC : C∈P) : (A∩C).card≤r-m := by
    have ind : (colorGraph c j).IsIndepSet ((A∩C : Finset V) : Set V) :=
      fun _ hx _ hy hxy e => ne ((clP C hC (mem_inter.mp hx).2 (mem_inter.mp hy).2 hxy).2.symm.trans e.2)
    exact (card_le_rankOn _ inter_subset_left ind).trans rj
  have qbound := card_biUnion_le (s:=Q) (t:=id) |>.trans (sum_le_sum sizeQ)
  have pbound := card_biUnion_le (s:=P) (t:=fun C => A∩id C) |>.trans (sum_le_sum sizeP)
  rw [←inter_biUnion] at pbound
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,cq,cp] at qbound pbound
  have first := card_sdiff_add_card_eq_card (subset_univ (Q.biUnion id))
  change A.card+(Q.biUnion id).card=Fintype.card V at first
  rw [hn] at first
  have second := card_inter_add_card_sdiff A (P.biUnion id)
  change (A∩P.biUnion id).card+R.card=A.card at second
  have eq := Nat.sub_add_cancel hm
  have sufficient : (r-m)^2+1≤R.card := by
    nlinarith only [qbound,pbound,first,second,congrArg (·^2) eq,congrArg (m*·) eq]
  obtain ⟨U,sub,n⟩ := exists_subset_card_eq sufficient
  exact ⟨U,n,(rankOn_mono _ (sub.trans (fun x hx => mem_sdiff.mpr
    ⟨mem_univ x,(mem_sdiff.mp hx).2⟩))).trans ri,(rankOn_mono _ (sub.trans sdiff_subset)).trans rj⟩

end Erdos617
