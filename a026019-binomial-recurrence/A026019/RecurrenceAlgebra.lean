module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

namespace A026019

/-- Polynomial elimination of the binomial identities at three consecutive indices. -/
theorem recurrence_algebra (x b0 b1 b2 a0 a1 a2 : ℚ) (hx : 0 ≤ x)
    (ha0 : 2 * (x + 1) * (2 * x + 1) * (2 * x + 3) * a0 =
      (x + 3) * (7 * x ^ 2 + 6 * x + 2) * b0)
    (ha1 : 2 * (x + 1 + 1) * (2 * (x + 1) + 1) * (2 * (x + 1) + 3) * a1 =
      (x + 1 + 3) * (7 * (x + 1) ^ 2 + 6 * (x + 1) + 2) * b1)
    (ha2 : 2 * (x + 2 + 1) * (2 * (x + 2) + 1) * (2 * (x + 2) + 3) * a2 =
      (x + 2 + 3) * (7 * (x + 2) ^ 2 + 6 * (x + 2) + 2) * b2)
    (hb1 : 2 * (2 * x + 1) * (x + 1) * b1 =
      3 * (3 * x + 1) * (3 * x + 2) * b0)
    (hb2 : 2 * (2 * (x + 1) + 1) * (x + 1 + 1) * b2 =
      3 * (3 * (x + 1) + 1) * (3 * (x + 1) + 2) * b1) :
    -2 * (2 * (x + 2) + 3) * (13 * (x + 2) - 9) * (x + 2 + 1) * a2 +
      (499 * (x + 2) ^ 3 - 7 * (x + 2) ^ 2 - 120 * (x + 2) - 54) * a1 -
      3 * (3 * (x + 2) - 5) * (37 * (x + 2) - 24) * (3 * (x + 2) - 4) * a0 = 0 := by
  have hd0 : 2 * (x + 1) * (2 * x + 1) * (2 * x + 3) ≠ 0 := by positivity
  have hd1 : 2 * (x + 1 + 1) * (2 * (x + 1) + 1) * (2 * (x + 1) + 3) ≠ 0 := by
    positivity
  have hd2 : 2 * (x + 2 + 1) * (2 * (x + 2) + 1) * (2 * (x + 2) + 3) ≠ 0 := by
    positivity
  have he1 : 2 * (2 * x + 1) * (x + 1) ≠ 0 := by positivity
  have he2 : 2 * (2 * (x + 1) + 1) * (x + 1 + 1) ≠ 0 := by positivity
  have ha0' := (eq_div_iff hd0).2 ((mul_comm a0 _).trans ha0)
  have ha1' := (eq_div_iff hd1).2 ((mul_comm a1 _).trans ha1)
  have ha2' := (eq_div_iff hd2).2 ((mul_comm a2 _).trans ha2)
  have hb1' := (eq_div_iff he1).2 ((mul_comm b1 _).trans hb1)
  have hb2' := (eq_div_iff he2).2 ((mul_comm b2 _).trans hb2)
  rw [ha2', ha1', ha0', hb2', hb1']
  field_simp
  ring

end A026019
