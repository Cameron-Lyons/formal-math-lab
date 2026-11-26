module

public import Coloring
public import Cycles
public import Edges

@[expose] public section

namespace Erdos835

open Finset

/-- Two fixed vertices in an invariant 18-set pick out a fixed edge color.
The matching of this color pairs all fixed vertices in the set. -/
theorem even_fixed_on_18 {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (W : Finset Point) (hW : W.card = 18) (hmap : W.map g.toEmbedding = W)
    (hfixed : 1 < (W.filter fun x => g x = x).card) :
    Even (W.filter fun x => g x = x).card := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hfixed
  obtain ⟨hxW, hx⟩ := mem_filter.mp hx
  obtain ⟨hyW, hy⟩ := mem_filter.mp hy
  have hmem : y ∈ W.erase x := mem_erase.mpr ⟨hxy.symm, hyW⟩
  have hcard : ((W.erase x).erase y).card = 16 := by
    simp [card_erase_of_mem hmem, card_erase_of_mem hxW, hW]
  let i := c ⟨_, hcard⟩
  have hcol : EdgeHasColor c W i x y := ⟨hxy, hcard, rfl⟩
  have hfixCol : τ i = i := edge_color_unique (by simpa [hx, hy] using edge_map he hmap hcol) hcol
  apply even_fixed_of_matching W g hmap (EdgeHasColor c W i)
      (fun h => edge_symm h) (fun v => edge_irrefl v) (edge_unique hc hW i)
  intro a b h
  simpa only [hfixCol] using edge_map he hmap h

/-- No order-11 or order-13 permutation of the points can act on a rainbow
coloring at k = 16, even if it is allowed to permute all seventeen colors. -/
theorem no_order11_or_13 {c : Block → Fin 17} (hc : Rainbow c)
    (g : Equiv.Perm Point) (hg : orderOf g = 11 ∨ orderOf g = 13) (τ : Equiv.Perm (Fin 17)) :
    ¬ Equivariant c g τ := by
  intro he
  have hp : (orderOf g).Prime := by rcases hg with h | h <;> rw [h] <;> decide
  obtain ⟨W, hW, hm, hF⟩ := primeOrder_witness18 hp (by omega) (by omega) g rfl
  have hmany : 1 < (W.filter fun x => g x = x).card := by rw [hF]; omega
  obtain ⟨m, hm'⟩ := even_fixed_on_18 hc he W hW hm hmany
  rw [hF] at hm'
  omega

end Erdos835
