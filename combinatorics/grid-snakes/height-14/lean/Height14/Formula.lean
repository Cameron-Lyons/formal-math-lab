import Std

namespace Height14

/-- The height-14 length formula, including the exceptional small widths.
    The value at zero is convenient for an empty board. -/
def formula (n : Nat) : Nat :=
  if n < 18 then
    #[0,14,21,30,38,46,55,64,72,82,89,98,107,115,123,134,142,150][n]!
  else
    52 * (n / 6) + #[3,12,20,30,38,47][n % 6]!

theorem formula_add_six {n : Nat} (hn : 18 ≤ n) :
    formula (n + 6) = formula n + 52 := by
  have hq : (n + 6) / 6 = n / 6 + 1 := by omega
  have hr : (n + 6) % 6 = n % 6 := by omega
  simp only [formula, ite_eq_right (show ¬ n + 6 < 18 by omega),
    ite_eq_right (show ¬ n < 18 by omega), hq, hr, Nat.mul_add, Nat.mul_one]
  omega

end Height14
