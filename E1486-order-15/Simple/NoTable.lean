import Simple.Check
import Simple.Order
import Simple.FewSquares
import Simple.ManySquares
import Simple.MiddleCases

namespace E1486.Simple

/-- A hypothetical table has four to eleven squares. The finite step only
needs the 36 possible fixed-point/pair patterns within those eight sizes. -/
theorem noTable : ¬ ∃ op : Fin 15 → Fin 15 → Fin 15,
    ∀ x y z, op (op y x) (op x (op z z)) = x := by
  rintro ⟨table, satisfies⟩
  -- Label the k squares first, starting with the j squares fixed by squaring.
  obtain ⟨op, k, j, law, labels, ordered⟩ := exists_ordered (m := table) satisfies

  -- The two counting arguments give 4 ≤ k ≤ 11.
  have lower : 4 ≤ k := four_le_square_labels law labels.le_size
    (fun q hq => (labels.sq_iff q).mp hq)
  have upper : k ≤ 11 := Counting.at_most_eleven (arrows op) (fromLaw law) labels.le_size
    (fun q => (marked_iff_square law q).trans (labels.sq_iff q))

  -- The graph of our table passes the test. Every remaining case fails it.
  have passes := check_of_law law labels
  have fails := Finite.middle_refute k j lower upper labels.le_squares labels.parity
    (pack (arrows op)) (pack (fun a b => arrows op b a))
  rw [passes, ordered] at fails
  contradiction

end E1486.Simple
