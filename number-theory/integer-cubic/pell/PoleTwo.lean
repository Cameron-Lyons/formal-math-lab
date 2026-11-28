module

public import SmallCubic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Algebraic steps in the pole-order-two reduction. -/
public section

namespace SmallCubic

/-- The two highest Laurent coefficients of w² = y⁴+8−4x³, at a pole
of order two of x. These identities control loss of pole order on reduction. -/
theorem pole_two_leading_coefficients {K : Type*} [Field K] [CharZero K]
    (x₂ x₁ w₃ w₂ : K) (hx : x₂ ≠ 0) (h₆ : w₃ ^ 2 = -4 * x₂ ^ 3)
    (h₅ : 2 * w₃ * w₂ = -12 * x₂ ^ 2 * x₁) :
    ∃ s : K, s ^ 2 = -x₂ ∧ w₃ = 2 * s ^ 3 ∧ w₂ = -3 * s * x₁ := by
  let s := -w₃ / (2 * x₂)
  have hs : s ^ 2 = -x₂ := by
    dsimp [s]
    field_simp
    linear_combination h₆
  have hp : 2 * x₂ * s = -w₃ := by dsimp [s]; field_simp
  have h₃ : w₃ = 2 * s ^ 3 := by linear_combination hp - 2*s*hs
  have h₃nz : w₃ ≠ 0 := by
    rintro rfl
    simp [hx] at h₆
  refine ⟨s, hs, h₃, ?_⟩
  apply mul_left_cancel₀ h₃nz
  calc w₃ * w₂ = -6 * x₂ ^ 2 * x₁ := by linear_combination (1/2 : K)*h₅
    _ = w₃ * (-3 * s * x₁) := by
      linear_combination 3*s*x₁*hp - 6*x₂*x₁*hs

/-- In the residue field, loss of the second-order x coefficient forces
loss of the first-order y coefficient at the same end. -/
theorem pole_two_dropped_pole {k : Type*} [Field k]
    (x₂ x₁ x₀ w₃ w₂ w₁ y₁ s : k)
    (hs : s ^ 2 = -x₂) (h₃ : w₃ = 2 * s ^ 3) (h₂ : w₂ = -3 * s * x₁)
    (h₄ : w₂ ^ 2 + 2 * w₃ * w₁ = y₁ ^ 4 - 12 * x₂ * (x₁ ^ 2 + x₂ * x₀))
    (hx : x₂ = 0) : y₁ = 0 := by
  subst x₂
  have hs0 : s = 0 := by simpa using hs
  subst s
  simpa [h₃, h₂] using h₄.symm

/-- After the two involutions are imposed, write t' for c/t. The descended
quadratic factor is visible without divisions, including at a zero of w. -/
theorem pole_two_symmetric_factor {R : Type*} [CommRing R]
    (t t' A B H J : R) :
    A*t^2 + B + A*t'^2 = A*(t+t')^2 + (B - 2*A*(t*t')) ∧
    (H*(t^3-t'^3) + J*(t-t'))^2 =
      ((t+t')^2 - 4*(t*t')) * (H*((t+t')^2 - t*t')+J)^2 := by
  constructor <;> ring

/-- The square factor forced by the finite-field involutions contradicts
the existence of an integral triple. Its coefficients may lie in a field
extension, while the graph x = a y² + b is rational. -/
theorem pole_two_square_factor_excluded {K : Type*} [Field K] [CharZero K]
    (a b : ℚ) (ha : a ≠ 0) (x y z : ℤ) (hxyz : Solves x y z)
    (hx : (x : ℚ) = a*(y : ℚ)^2 + b) (c v e : K) (hv : v ≠ 0)
    (h : ∀ s : K, s^2 + 8 - 4*((a : K)*s + b)^3 =
      (s-4*c)*(v*(s-c)+e)^2) : False := by
  let r := c - e/v
  have hr : v*(r-c)+e = 0 := by dsimp [r]; field_simp; ring
  have hf : r^2 + 8 - 4*((a : K)*r + b)^3 = 0 := by simp [h r, hr]
  have hd : 2*r - 12*(a : K)*((a : K)*r + b)^2 = 0 := by
    linear_combination (2/3 : K)*(h (r+1) - h (r-1)) -
      (1/12 : K)*(h (r+2) - h (r-2)) + (v*(r-c)+e+2*v*(r-4*c))*hr
  obtain ⟨q, _, hq, hq'⟩ := rational_multiple_root_of_cubic
    (-4*a^3) (1-12*a^2*b) (-12*a*b^2) (8-4*b^3) (by simp [ha]) r
    (by push_cast; linear_combination hf) (by push_cast; linear_combination hd)
  exact no_rational_contact a b q x y z hxyz hx
    (by linear_combination hq) (by linear_combination hq')

end SmallCubic
