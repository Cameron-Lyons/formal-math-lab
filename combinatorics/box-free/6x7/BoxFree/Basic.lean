import Std

namespace BoxFree

abbrev Layer := Fin 6 → Fin 7 → Bool
abbrev Coloring (n : Nat) := Fin n → Layer

/-- All four entries have the specified color. The caller orders the row and column indices. -/
def Rectangle (L : Layer) (a b : Fin 6) (i j : Fin 7) (v : Bool) : Prop :=
  L a i = v ∧ L a j = v ∧ L b i = v ∧ L b j = v

/-- No two distinct layers realize the same colored rectangle. -/
def BoxFree {n : Nat} (C : Coloring n) : Prop :=
  ∀ (a b : Fin 6), a < b → ∀ (i j : Fin 7), i < j → ∀ (v : Bool) (z : Fin n),
    Rectangle (C z) a b i j v → ∀ w, z < w → ¬ Rectangle (C w) a b i j v

/-- Keep the first `m` layers of a coloring of height `n`. -/
def restrict {m n : Nat} (C : Coloring n) (h : m ≤ n) : Coloring m :=
  fun z => C (z.castLE h)

theorem boxFree_restrict {m n : Nat} {C : Coloring n} (hf : BoxFree C) (h : m ≤ n) :
    BoxFree (restrict C h) := by
  intro a b hab i j hij v z hz w hzw
  exact hf a b hab i j hij v (z.castLE h) hz (w.castLE h) hzw

end BoxFree
