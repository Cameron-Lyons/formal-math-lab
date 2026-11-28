import E670.Parts

/-!
# No model of equation 670 has ten elements
-/

namespace E670

/--
The formula has no model: every cube of `parts` is refuted by one of the part modules, and one
more certificate shows that no model of the formula avoids all the cubes.
-/
theorem formula_unsat : Unsat formula :=
  unsat_of_cubes (Refutes.flatten (parts := parts) parts_refuted) (by refute)

/-- No magma on ten elements satisfies `x = y ◇ (x ◇ ((x ◇ y) ◇ y))`. -/
theorem no_model_of_order_ten :
    ¬ ∃ op : Fin 10 → Fin 10 → Fin 10, ∀ x y, op y (op x (op (op x y) y)) = x := by
  rintro ⟨op, law⟩
  obtain ⟨op', law', chain', side'⟩ := exists_normal law
  exact formula_unsat (assign op') (sat_formula law' chain' side')

end E670
