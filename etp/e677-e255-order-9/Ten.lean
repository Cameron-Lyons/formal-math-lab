import Ten.Parts

/-!
# No ten-element model of Equation 677
-/

namespace Ten

open E670

/--
The formula has no model: every case in `parts` is refuted by one of the part modules, and one
more certificate shows that no model of the formula avoids all the cases.
-/
theorem formula_unsat : Unsat formula :=
  unsat_of_cubes (Refutes.flatten (parts := parts) parts_refuted) (by refute)

/-- No ten-element multiplication table obeys Equation 677. -/
theorem no_model : ¬ ∃ op : Fin 10 → Fin 10 → Fin 10, Eq677 op := by
  rintro ⟨op, h⟩
  obtain ⟨t, law, chain, side⟩ := exists_normal h
  exact formula_unsat (assign t) (sat_formula law chain side)

/-- In particular, every ten-element table obeying Equation 677 obeys Equation 255. -/
theorem eq677_implies_eq255 (op : Fin 10 → Fin 10 → Fin 10) (h : Eq677 op) : Eq255 op :=
  absurd ⟨op, h⟩ no_model

end Ten
