import Simple.TestOfLaw
import Simple.Order12.Cases

namespace E1486.Order12
open E1486.Simple E1486.Test

/-- No binary operation on 12 elements satisfies `(y⋆x)⋆(x⋆(z⋆z)) = x`. -/
theorem noTable : ¬ ∃ op : Fin 12 → Fin 12 → Fin 12,
    ∀ x y z, op (op y x) (op x (op z z)) = x := by
  rintro ⟨table, satisfies⟩
  -- Label the k squares first, starting with the j squares fixed by squaring.
  obtain ⟨op, k, j, law, labels⟩ := normalize_diagonal satisfies
  -- The arrows of this table pass the test. Every pattern fails it.
  have passes := check_of_law law labels
  have fails := refute k j labels.le_size labels.le_squares labels.parity (pack (arrows op))
  rw [passes] at fails
  contradiction

end E1486.Order12
