module

public import Erdos617.RowDescent

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {r : ℕ} (c : Sym2 V → Fin r)

/-- On a fixed set U, each color counted here can be avoided by some
s+1 vertices of U. Different colors can have different witnesses. -/
noncomputable def avoidableOn (U : Finset V) (s : ℕ) : Finset (Fin r) := by
  classical
  exact univ.filter fun j => s<rankOn (colorGraph c j) U

omit [DecidableEq V] in
theorem mem_avoidableOn (U : Finset V) (s : ℕ) (j : Fin r) :
    j ∈ avoidableOn c U s ↔ ∃ I⊆U,(colorGraph c j).IsNIndepSet (s+1) I := by
  classical
  simp only [avoidableOn,mem_filter,mem_univ,true_and]
  constructor
  · intro h
    obtain ⟨M,sub,ind,sz⟩ := exists_max_indep (colorGraph c j) U
    obtain ⟨I,hI,n⟩ := exists_subset_card_eq (s:=M) (show s+1≤M.card by omega)
    exact ⟨I,hI.trans sub,ind.mono hI,n⟩
  · rintro ⟨I,sub,ind⟩
    have le := card_le_rankOn (colorGraph c j) sub ind.isIndepSet
    rwa [ind.card_eq] at le

/-- If s colors cannot be avoided on U, retaining those colors and reassigning
the others gives a balanced s-coloring on U. Otherwise at least r−s+1 original
colors can individually be avoided. -/
theorem merge_or_many_avoidable (U : Finset V) {s : ℕ} (hs : 0<s) :
    (∃ f : Fin r → Fin s, Balanced
      (f ∘ (fun e : Sym2 U => c (Sym2.map Subtype.val e)))) ∨
      r+1≤s+(avoidableOn c U s).card := by
  classical
  by_cases small : r+1≤s+(avoidableOn c U s).card
  · exact Or.inr small
  left
  let L := (avoidableOn c U s)ᶜ
  have size : L.card+(avoidableOn c U s).card=r := by simp [L]
  obtain ⟨T,hT,sz⟩ := exists_subset_card_eq (s:=L) (show s≤L.card by omega)
  let d := fun e : Sym2 U => c (Sym2.map Subtype.val e)
  apply balanced_merge_of_disjoint_groups (ι:=T) hs ((Fintype.card_coe T).trans sz) d (fun i => {i.val})
  · intro i j ne
    simpa using (show i.val≠j.val from fun h => ne (Subtype.ext h))
  · intro j I hi
    by_contra! miss
    have ind : (colorGraph d j.val).IsNIndepSet (s+1) I := by
      refine ⟨?_,hi⟩
      intro a ha b hb ne e
      exact miss a ha b hb ne (mem_singleton.mpr e.2)
    obtain ⟨W,sub,ind'⟩ := lift_independent_subset c j.val U ⟨I,ind⟩
    exact (mem_compl.mp (hT j.prop)) ((mem_avoidableOn ..).mpr ⟨W,sub,ind'⟩)

/-- On the two-row square of an arbitrary counterexample, either the
coloring descends two palette sizes, or at least three further colors are
avoidable on sets of r−1 vertices inside this same square. -/
theorem two_row_palette_descent [Fintype V] (hr : 5≤r) (hn : Fintype.card V=r^2+1) (hb : Balanced c) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(r-2)^2+1 ∧
      i∉avoidableOn c U (r-2) ∧ j∉avoidableOn c U (r-2) ∧
      ((∃ f : Fin r → Fin (r-2), Balanced (f ∘ (fun e : Sym2 U => c (Sym2.map Subtype.val e)))) ∨
        3≤(avoidableOn c U (r-2)).card) := by
  classical
  obtain ⟨i,j,U,ne,sz,li,lj⟩ := exists_two_row_square hr hn hb
  refine ⟨i,j,U,ne,sz,by simpa [avoidableOn] using li,by simpa [avoidableOn] using lj,?_⟩
  rcases merge_or_many_avoidable c U (show 0<r-2 by omega) with merge|many
  · exact Or.inl merge
  · exact Or.inr (by omega)

end Erdos617
