import Mathlib.Tactic

namespace Erdos677.SixElliptic

/-- The elliptic model for the ratio `u/v`, expressed without denominators. -/
def cubic (u v x : ℚ) : ℚ :=
  x^3 - 8*u*v*x^2 + 5*u^2*v^2*x + 9*u^4*v^2 + 9*u^2*v^4 + 32*u^3*v^3

def quartic (u v t : ℚ) : ℚ :=
  v^2*t^4 + 3*u*v*t^3 - 8*u*v*t^2 + 3*u*v*t + u^2

/-- Taking the slope `t=b/a` of a line through the rational point (0,0)
gives a quadratic in `a`. Completing its square yields this quartic. -/
theorem plane_to_quartic {u v a b t : ℚ} (ha : a ≠ 0) (hb : b = a*t)
    (h : v*b*(b-1)*(b-3) = u*a*(a-1)*(a-3)) :
    ((v*t^3-u)*a - 2*(v*t^2-u))^2 = quartic u v t := by
  subst b
  have hzero : a * ((v*t^3-u)*a^2 - 4*(v*t^2-u)*a + 3*(v*t-u)) = 0 := by
    linear_combination h
  have hpoly := (mul_eq_zero.mp hzero).resolve_left ha
  unfold quartic
  linear_combination (v*t^3-u) * hpoly

/-- The denominator-cleared formulas for the quartic-to-Weierstrass map. -/
theorem quartic_to_elliptic {u v t z x y : ℚ} (hu : u ≠ 0) (ht : t ≠ 0)
    (hz : z^2 = quartic u v t)
    (hx : x*t^2 = 2*u*(z+u) + 3*u*v*t)
    (hy : 2*u*y = (x^2-4*u^2*v^2)*t - 3*u*v*x - 6*u^3*v) :
    y^2 = cubic u v x := by
  let H := (x^2-4*u^2*v^2)*t^2 - (6*u*v*x+12*u^3*v)*t +
    (9*u^2*v^2-4*u^2*x+32*u^3*v)
  have hprod : t^2 * H = 0 := by
    unfold H
    unfold quartic at hz
    linear_combination (x*t^2-3*u*v*t-2*u^2+2*u*z)*hx + 4*u^2*hz
  have hH := (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ ht)
  have hfinal : (2*u)^2 * (y^2 - cubic u v x) = 0 := by
    unfold cubic
    unfold H at hH
    linear_combination
      (2*u*y+(x^2-4*u^2*v^2)*t-3*u*v*x-6*u^3*v)*hy + (x^2-4*u^2*v^2)*hH
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfinal).resolve_left (by positivity))

/-- In the positive part of each of the four plane cubics the forward map is
always defined. The returned coordinates are rational, even for integral input. -/
theorem plane_to_elliptic {u v a b : ℚ} (hu : u ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : v*b*(b-1)*(b-3) = u*a*(a-1)*(a-3)) :
    let t := b/a
    let z := (v*t^3-u)*a - 2*(v*t^2-u)
    let x := (2*u*(z+u)+3*u*v*t)/t^2
    let y := ((x^2-4*u^2*v^2)*t-3*u*v*x-6*u^3*v)/(2*u)
    y^2 = cubic u v x := by
  dsimp only
  have ht := div_ne_zero hb ha
  apply quartic_to_elliptic hu ht
  · exact plane_to_quartic ha (by field_simp) h
  · apply div_mul_cancel₀ _ (pow_ne_zero _ ht)
  · rw [mul_comm]
    apply div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hu)

end Erdos677.SixElliptic
