import Simple.LeaderOfLaw
import Simple.Order14.Cases

namespace E1486.Order14
open E1486.Simple E1486.Test

/-- No binary operation on 14 elements satisfies `(y⋆x)⋆(x⋆(z⋆z)) = x`. -/
theorem noTable : ¬ ∃ op : Fin 14 → Fin 14 → Fin 14,
    ∀ x y z, op (op y x) (op x (op z z)) = x := by
  rintro ⟨table, satisfies⟩
  -- Label the k squares first, starting with the j squares fixed by squaring, so that
  -- no swap of neighboring labels increases the string of arrows.
  obtain ⟨op, k, j, law, labels, leading⟩ := exists_leading satisfies
  -- The arrows of this table pass both tests. Every pattern fails one of them.
  have passes := check_of_law law labels
  have fails := refute k j labels.le_size labels.le_squares labels.parity (pack (arrows op))
  rw [passes, leading] at fails
  contradiction

end E1486.Order14
