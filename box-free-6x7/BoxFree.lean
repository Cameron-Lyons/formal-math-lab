import BoxFree.Construction
import BoxFree.Upper

namespace BoxFree

/-- A red-blue coloring of the 6 × 7 × n grid can avoid monochromatic boxes
exactly for heights up to and including 52. -/
theorem exists_boxFree_iff (n : Nat) : (∃ C : Coloring n, BoxFree C) ↔ n ≤ 52 := by
  constructor
  · rintro ⟨C, free⟩
    exact height_le_52 free
  · intro h
    exact ⟨restrict coloring52 h, boxFree_restrict coloring52_boxFree h⟩

end BoxFree
