import Erdos617.SevenColors
import Erdos617.EightColors
import Erdos617.NineColors
import Erdos617.TenColors

namespace Erdos617

/-- Every coloring in the exact conjecture range through ten colors has
a set of r+1 vertices missing a color. -/
theorem missing_of_at_most_ten_colors {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 3≤r) (upper : r≤10) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) :
    ∃ (S : Finset V) (k : Fin r), S.card=r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u≠v → c s(u,v)≠k := by
  rcases show r≤6 ∨ r=7 ∨ r=8 ∨ r=9 ∨ r=10 by omega with small|rfl|rfl|rfl|rfl
  · exact missing_of_at_most_six_colors hr small hn c
  · exact seven_colors hn c
  · exact eight_colors hn c
  · exact nine_colors hn c
  · exact ten_colors hn c

/-- Rank at most four can never be the first obstruction for any palette
of at least seven colors, independently of the ambient number of vertices. -/
theorem MinimalObstruction.five_le_of_seven_le {V : Type*} [DecidableEq V] {r t : ℕ}
    {c : Sym2 V → Fin r} {k : Fin r} {S : Finset V} (h : MinimalObstruction c k t S)
    (hr : 7≤r) (hb : Balanced c) (ht : t<r) : 5≤t := by
  rcases show r=7 ∨ r=8 ∨ 9≤r by omega with rfl|rfl|large
  · obtain ⟨_,_,_,_,_,_,half,_,two,_⟩ := h.exists_nested_product_obstruction (by decide) hb ht
    by_contra! low
    obtain rfl : t=4 := by omega
    exact h.not_seven_four hb
  · obtain ⟨_,_,_,_,_,_,half,_,two,_⟩ := h.exists_nested_product_obstruction (by decide) hb ht
    by_contra! low
    obtain rfl : t=4 := by omega
    exact h.not_eight_four hb
  · exact h.five_le_of_nine_le hb large ht

/-- In every balanced coloring on any vertex type, each set of 4r+1
vertices contains five vertices avoiding any prescribed color, for r≥7. -/
theorem independent_five_in_subset_of_seven_le {V : Type*} [DecidableEq V] {r : ℕ}
    (hr : 7≤r) (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (S : Finset V)
    (size : S.card=4*r+1) : ∃ I⊆S, (colorGraph c k).IsNIndepSet 5 I := by
  classical
  by_contra! no
  obtain ⟨t,W,ht,_,h⟩ := minimalObstruction_of_failure size no
  have := h.five_le_of_seven_le hr hb (by omega)
  omega

end Erdos617
