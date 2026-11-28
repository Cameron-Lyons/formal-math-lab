import Laws
import E670.Cubes

/-!
# Equation 677 on ten elements

A ten-element table that obeys Equation 677 can be renamed so that

* `0 ⋆ y ≤ y + 1` for every `y`, and
* either `0 ⋆ 0 ≠ 0` or every element is idempotent.

`formula` lists clauses that hold in every such table; `sat_formula` proves this.

The renaming, the table encoding and the case-by-case refutation come from the Equation 670
project, which treats the same kind of table.
-/

namespace Ten

open E670
-- Re-export `Refutes` so the generated `Ten.Part.*` modules can refer to it unqualified.
export E670 (Refutes)

variable {op : Op}

/-- Every row contains every element. -/
theorem left_surjective (h : Eq677 op) (y x : Fin 10) : ∃ w, op y w = x :=
  ⟨_, (h x y).symm⟩

/-- No row contains an element twice. -/
theorem left_injective (h : Eq677 op) {y a b : Fin 10} (hab : op y a = op y b) : a = b :=
  injective_of_surjective (left_surjective h y) hab

/-- Equation 677, read as an implication between four entries of the table. -/
theorem law_entry (h : Eq677 op) {x y a b c : Fin 10}
    (h1 : op y x = a) (h2 : op a y = b) (h3 : op x b = c) : op y c = x := by
  subst h1 h2 h3
  exact (h x y).symm

/-- The same four entries, with row `y` cancelled. -/
theorem law_entry_cancel (h : Eq677 op) {x y a b c : Fin 10}
    (h1 : op y x = a) (h2 : op a y = b) (h4 : op y c = x) : op x b = c :=
  left_injective h ((law_entry h h1 h2 rfl).trans h4.symm)

/-- The same four entries, with rows `y` and `x` cancelled. -/
theorem law_entry_cancel₂ (h : Eq677 op) {x y a b c : Fin 10}
    (h1 : op y x = a) (h3 : op x b = c) (h4 : op y c = x) : op a y = b :=
  left_injective h ((law_entry_cancel h h1 rfl h4).trans h3.symm)

theorem rename_law {s : Fin 10 → Fin 10} (hs : ∀ x, s (s x) = x) (h : Eq677 op) :
    Eq677 (rename s op) := by
  intro x y
  simp only [rename, hs]
  rw [← h (s x) (s y), hs]

/-- Every ten-element table that obeys Equation 677 can be renamed into normal form. -/
theorem exists_normal (h : Eq677 op) :
    ∃ t : Op, Eq677 t ∧ ChainRow t ∧ (t 0 0 = 0 → ∀ x, t x x = x) :=
  exists_normal_of (fun _ _ hs => rename_law hs) h

/-- With `a = y ⋆ x`, `b = a ⋆ y` and `c = x ⋆ b`, Equation 677 says `y ⋆ c = x`. -/
def lawClauses : List Cl :=
  R.flatMap fun x => R.flatMap fun y => R.flatMap fun a => R.flatMap fun b => R.flatMap fun c =>
    [[neg y x a, neg a y b, neg x b c, pos y c x],
     [neg y x a, neg a y b, neg y c x, pos x b c],
     [neg y x a, neg x b c, neg y c x, pos a y b]]

/-- Clauses that hold in every ten-element table that obeys Equation 677 and is in normal form. -/
def formula : List Cl :=
  cellClauses ++ rowClauses ++ lawClauses ++ chainUnits ++ sideClauses

theorem sat_formula (law : Eq677 op) (chain : ChainRow op)
    (side : op 0 0 = 0 → ∀ x, op x x = x) : ∀ c ∈ formula, csat (assign op) c = true := by
  intro cl hc
  simp only [formula, List.mem_append] at hc
  rcases hc with (((hc | hc) | hc) | hc) | hc
  · exact sat_cellClauses op cl hc
  · exact sat_rowClauses (left_surjective law) (left_injective law) cl hc
  · -- Equation 677
    simp only [lawClauses, R, List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
      List.mem_finRange, true_and, or_false] at hc
    obtain ⟨x, y, a, b, c, rfl | rfl | rfl⟩ := hc <;>
      simp only [csat_neg, csat_pos, csat_nil, or_false]
    · exact law_entry law
    · exact law_entry_cancel law
    · exact law_entry_cancel₂ law
  · exact sat_chainUnits chain cl hc
  · exact sat_sideClauses side cl hc

end Ten
