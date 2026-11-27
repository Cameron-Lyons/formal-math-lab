import Std

namespace BoxFree5x8

abbrev Layer := Fin 5 → Fin 8 → Bool
abbrev Coloring (n : Nat) := Fin n → Layer

def Rectangle (L : Layer) (r s : Fin 5) (i j : Fin 8) (v : Bool) : Prop :=
  L r i = v ∧ L r j = v ∧ L s i = v ∧ L s j = v

/-- An ordered choice of two rows, columns and layers cannot have eight equal corners. -/
def BoxFree {n : Nat} (C : Coloring n) : Prop :=
  ∀ (r s : Fin 5), r < s → ∀ (i j : Fin 8), i < j → ∀ (v : Bool) (z : Fin n),
    Rectangle (C z) r s i j v → ∀ w, z < w → ¬ Rectangle (C w) r s i j v

/-- A column mask has bit r set precisely when row r is red. -/
private def seeds : Vector (Vector (BitVec 5) 8) 3 := #v[
  #v[6, 25, 26, 14, 20, 21, 3, 13],
  #v[9, 26, 22, 3, 14, 17, 28, 5],
  #v[10, 18, 17, 22, 12, 7, 5, 25]
]

/-- Rotate within the first two triples of columns, fixing columns 6 and 7. -/
private def column (c : Fin 8) (shift : Nat) : Fin 8 :=
  if h : c.val < 6 then ⟨3 * (c.val / 3) + (c.val % 3 + shift) % 3, by omega⟩ else c

/-- Take all five row rotations and all three column rotations of each seed. -/
def coloring45 (z : Fin 45) (r : Fin 5) (c : Fin 8) : Bool :=
  let seed := seeds[z.val / 15]'(by omega)
  seed[column c (z.val / 5)].getLsbD ((r.val + z.val) % 5)

theorem coloring45_boxFree : BoxFree coloring45 := by
  unfold BoxFree Rectangle
  decide +kernel

/-- Exactly the colored rectangles on the last two columns are unused. -/
theorem rectangle_coverage : ∀ (r s : Fin 5), r < s → ∀ (i j : Fin 8), i < j →
    ∀ v : Bool, (∃ z : Fin 45, Rectangle (coloring45 z) r s i j v) ↔ i < 6 := by
  unfold Rectangle
  decide +kernel

/-- The first n layers of the witness give every height through 45, including 43. -/
theorem exists_boxFree_of_le {n : Nat} (h : n ≤ 45) : ∃ C : Coloring n, BoxFree C := by
  refine ⟨fun z => coloring45 (z.castLE h), ?_⟩
  intro r s hrs i j hij v z hz w hzw
  exact coloring45_boxFree r s hrs i j hij v (z.castLE h) hz (w.castLE h) hzw

theorem exists_boxFree_43 : ∃ C : Coloring 43, BoxFree C :=
  exists_boxFree_of_le (by decide)

end BoxFree5x8
