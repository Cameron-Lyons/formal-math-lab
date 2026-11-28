import Std

namespace SevenCycle

abbrev Color := Fin 3

/-- A three-coloring of the undirected edges of `Kₙ`. Values on the diagonal
are immaterial because the vertices of a simple cycle are distinct. -/
structure Coloring (n : Nat) where
  edge : Fin n → Fin n → Color
  symm : ∀ i j, edge i j = edge j i

def jump (a b : Color) : Nat := if a = b then 0 else 1

/-- Compare successive edge colors cyclically, including the comparison at
which the last edge meets the first. -/
def changes (edge : α → α → Color) (vs : List α) : Nat :=
  let es := vs.zipWith edge (vs.rotateLeft 1)
  (es.zipWith jump (es.rotateLeft 1)).sum

/-- A cyclic listing of seven distinct vertices with at most two changes. -/
def HasGoodSeven (c : Coloring n) : Prop :=
  ∃ vs : List (Fin n), vs.length = 7 ∧ vs.Nodup ∧ changes c.edge vs ≤ 2

def ForcesSeven (n : Nat) : Prop := ∀ c : Coloring n, HasGoodSeven c

end SevenCycle
