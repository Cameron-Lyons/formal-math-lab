import Mathlib.Tactic.LinearCombination

namespace Erdos677

/-- If two centered five-term products have ratio `b/a`, the ratio of their
centers is the first coordinate of a rational point on an explicit sextic. -/
theorem five_ratio_sextic {a b X Y : ℚ} (hX : X ≠ 0)
    (hprod : a * (Y * (Y^2 - 1) * (Y^2 - 4)) =
             b * (X * (X^2 - 1) * (X^2 - 4))) :
    let t := Y / X
    ∃ z : ℚ, z^2 = 25 * (a * t^3 - b)^2 - 16 * (a * t^5 - b) * (a * t - b) := by
  intro t
  rw [show Y = t * X from (div_mul_cancel₀ Y hX).symm] at hprod
  -- Substituting Y = tX and cancelling X gives a quadratic in X².
  have hquad : (a * t^5 - b) * X^4 - 5 * (a * t^3 - b) * X^2 + 4 * (a * t - b) = 0 := by
    apply (mul_eq_zero_iff_left hX).mp
    linear_combination hprod
  -- Completing the square gives this square root of the discriminant.
  refine ⟨2 * (a * t^5 - b) * X^2 - 5 * (a * t^3 - b), ?_⟩
  linear_combination 4 * (a * t^5 - b) * hquad

end Erdos677
