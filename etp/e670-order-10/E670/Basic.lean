/-!
# Equation 670

`x = y ◇ (x ◇ ((x ◇ y) ◇ y))`, equation 670 of the Equational Theories Project.

In a finite model every row `z ↦ y ◇ z` of the table is a permutation: the law exhibits a
preimage of every `x`, and a surjection of a finite set onto itself is injective.
-/

namespace E670

/-- Equation 670. -/
def Law {S : Type} (op : S → S → S) : Prop :=
  ∀ x y, op y (op x (op (op x y) y)) = x

/-- A surjection of `Fin n` onto itself is injective. -/
theorem injective_of_surjective {n : Nat} {f : Fin n → Fin n} (hs : ∀ b, ∃ a, f a = b)
    {a b : Fin n} (hab : f a = f b) : a = b := by
  apply Decidable.byContradiction
  intro hne
  -- otherwise the `n - 1` arguments other than `a` would take all `n` values
  have hsub : List.finRange n ⊆ ((List.finRange n).erase a).map f := by
    intro c _
    obtain ⟨x, rfl⟩ := hs c
    by_cases hx : x = a
    · rw [hx, hab]
      exact List.mem_map_of_mem ((List.mem_erase_of_ne (Ne.symm hne)).mpr (List.mem_finRange b))
    · exact List.mem_map_of_mem ((List.mem_erase_of_ne hx).mpr (List.mem_finRange x))
  have hlen := (List.nodup_finRange n).length_le_of_subset hsub
  rw [List.length_map, List.length_erase_of_mem (List.mem_finRange a), List.length_finRange] at hlen
  have := a.pos
  omega

variable {n : Nat} {op : Fin n → Fin n → Fin n}

/-- Every row contains every element. -/
theorem left_surjective (h : Law op) (y x : Fin n) : ∃ w, op y w = x :=
  ⟨_, h x y⟩

/-- No row contains an element twice. -/
theorem left_injective (h : Law op) {y a b : Fin n} (hab : op y a = op y b) : a = b :=
  injective_of_surjective (left_surjective h y) hab

/-- The law, read as an implication between four entries of the table. -/
theorem law_entry (h : Law op) {x y a b c : Fin n}
    (h1 : op x y = a) (h2 : op a y = b) (h3 : op x b = c) : op y c = x := by
  subst h1 h2 h3
  exact h x y

/-- The same four entries, with row `y` cancelled. -/
theorem law_entry_cancel (h : Law op) {x y a b c : Fin n}
    (h1 : op x y = a) (h2 : op a y = b) (h4 : op y c = x) : op x b = c :=
  left_injective h ((law_entry h h1 h2 rfl).trans h4.symm)

/-- The same four entries, with rows `y` and `x` cancelled. -/
theorem law_entry_cancel₂ (h : Law op) {x y a b c : Fin n}
    (h1 : op x y = a) (h3 : op x b = c) (h4 : op y c = x) : op a y = b :=
  left_injective h ((law_entry_cancel h h1 rfl h4).trans h3.symm)

end E670
