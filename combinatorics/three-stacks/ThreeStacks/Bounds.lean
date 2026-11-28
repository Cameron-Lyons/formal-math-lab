import ThreeStacks.Upper
import ThreeStacks.Coverage

namespace ThreeStacks

/-- Some permutation of 1 through n has no legal sorting schedule. -/
def Obstruction (n : Nat) : Prop := ∃ p, IsDeck n p ∧ ¬ Sortable n p

def IsMinimum (n : Nat) : Prop :=
  Obstruction n ∧ ∀ k, k < n → ¬ Obstruction k

theorem obstruction21 : Obstruction 21 := ⟨published, published_isDeck, published_unsortable⟩

/-- The short inference from the exhaustive length-19 result. -/
theorem smallest_of_all19 (h19 : ∀ p, IsDeck 19 p → Sortable 19 p) :
    IsMinimum 20 ∨ IsMinimum 21 := by
  have lower (k : Nat) (hk : k < 20) : ¬ Obstruction k := by
    rintro ⟨p, deck, fails⟩
    exact fails (allShorter h19 k (by omega) p deck)
  by_cases h20 : Obstruction 20
  · exact Or.inl ⟨h20, lower⟩
  · refine Or.inr ⟨obstruction21, ?_⟩
    intro k hk
    by_cases eq : k = 20
    · simpa [eq] using h20
    · exact lower k (by omega)

/-- The same bound with only the external bulk enumeration as a premise. -/
theorem smallest_of_bulk_coverage (bulk : Bulk19Coverage) :
    IsMinimum 20 ∨ IsMinimum 21 :=
  smallest_of_all19 (all19_of_bulk bulk)

end ThreeStacks
