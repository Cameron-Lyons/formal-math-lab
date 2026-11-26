module

public import Cyclic
public import Nine
public import Pairs

@[expose] public section

namespace Erdos835

open Finset

/-- If nine colors were fixed by a fixed-point-free involution, the unions
of eight point-pairs would induce a rainbow nine-coloring on pair indices.
Eleven such indices already contradict the divisibility of 55 by 3. -/
theorem fixedFree_palette_lt_nine {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (hinv : ∀ x, g (g x) = x) (hfree : ∀ x, g x ≠ x) :
    Fintype.card (Function.fixedPoints τ) < 9 := by
  classical
  by_contra! hge
  have hn := Nat.le_antisymm (fixedFree_palette_bound hc he hinv hfree) hge
  let I := Function.fixedPoints τ
  have : Nonempty I := Fintype.card_pos_iff.mp (by change 0 < Fintype.card (Function.fixedPoints τ); omega)
  obtain ⟨U, hU, apart⟩ := eleven_pairs g hinv hfree
  let block (s : {S : Finset U // S.card = 8}) : Block :=
    ⟨pairUnion g s.val, by rw [pairUnion_card g apart, s.property]⟩
  let col (s : {S : Finset U // S.card = 8}) : I :=
    ⟨c (block s), by
      have h := he (block s)
      have e : (block s).val.map g.toEmbedding = (block s).val := pairUnion_stable g hinv _
      exact h.symm.trans (congrArg c (Subtype.ext e))⟩
  apply no_rainbow_eight_on_eleven (V := U) (I := I) (by simpa using hU) col
  intro S hS
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simpa [I, hS] using hn.symm⟩
  intro i
  have hW : (pairUnion g S).card = 18 := by rw [pairUnion_card g apart, hS]
  have stable := pairUnion_stable g hinv S
  obtain ⟨x, hx, hedge⟩ := fixedColor_uses_pair hc he hW stable hinv hfree i.property
  obtain ⟨a, ha, hx'⟩ := (mem_pairUnion g S x).mp hx
  have edge : EdgeHasColor c (pairUnion g S) i.val a.val (g a.val) := by
    rcases hx' with rfl | rfl
    · exact hedge
    · simpa only [hinv] using edge_symm hedge
  refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
  obtain ⟨_, hcard, hcolor⟩ := edge
  let s : {S : Finset U // S.card = 8} :=
    ⟨S.erase a, by rw [card_erase_of_mem ha, hS]⟩
  change c (block s) = i.val
  exact (congrArg c (Subtype.ext (pairUnion_erase g apart S a)) :
    c (block s) = c ⟨_, hcard⟩).trans hcolor

/-- The palette action is an involution on 17 colors, so its fixed-point
count is odd. Combining this with the pair obstruction gives at most seven. -/
theorem fixedFree_palette_le_seven {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (hinv : ∀ x, g (g x) = x) (hfree : ∀ x, g x ≠ x) :
    Fintype.card (Function.fixedPoints τ) ≤ 7 := by
  have hg : g ^ 2 = 1 := Equiv.ext (fun x => by simpa [pow_two] using hinv x)
  have hτ := palette_pow_eq_one hc he hg
  have hm := Equiv.Perm.card_compl_support_modEq (σ := τ) (p := 2) (n := 1)
    (by simpa only [pow_one] using hτ)
  have hcard : Fintype.card (Function.fixedPoints τ) = τ.supportᶜ.card := by
    rw [Equiv.Perm.card_fixedPoints, τ.sum_cycleType, Finset.card_compl]
  have bound := fixedFree_palette_lt_nine hc he hinv hfree
  rw [← hcard, Fintype.card_fin] at hm
  change Fintype.card (Function.fixedPoints τ) % 2 = 17 % 2 at hm
  omega

end Erdos835
