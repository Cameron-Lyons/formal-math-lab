module

public import Mathlib.Data.Int.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Exact divisor test on the planes tangent to the cubic surface at
the points at infinity [−n:1:n³:0]. -/
public section
namespace SmallCubic.TangentAtInfinity

/-- The projective point at infinity determined by a coprime pair (a,b)
is [−a²b:a³:b³:0]. The tangent plane has the displayed gradient.
An affine integral point on it forces its first parameter to be a unit. -/
theorem tangent_parameter_unit (a b x y z : ℤ) (hc : IsCoprime a b)
    (hp : 3*a^4*b^2*x+2*a^3*b^3*y+a^6*z+b^6=0) : a=1 ∨ a= -1 := by
  have hd : a ∣ b^6 := ⟨-(3*a^3*b^2*x+2*a^2*b^3*y+a^5*z), by linear_combination hp⟩
  have h1 : a ∣ (1:ℤ) := hc.pow_right.dvd_of_dvd_mul_right (by simpa using hd : a ∣ 1*b^6)
  exact Int.isUnit_iff.mp (isUnit_of_dvd_one h1)

def H (a n : ℤ) := n^8+6*n^4*a-3*a^2

/-- The coordinates on the tangent plane reduce the cubic to a single
linear equation in the new variable m. -/
theorem plane_equation (a m n y : ℤ) (hy : 2*n*y=2*m-3*a-n^4) :
    4*((n^2*m)^2+y^2*(n^2*m)+(a-m)^3-2) =
      m*H a n - 4*(2-a^3) := by
  unfold H
  linear_combination m*(2*n*y+2*m-3*a-n^4)*hy

/-- A Bézout identity eliminates a from the two one-variable polynomials. -/
theorem plane_divisor (a m n : ℤ) (hm : m*H a n=4*(2-a^3)) :
    H a n ∣ 4*(n^24+540*n^12-108) := by
  let t := n^4
  refine ⟨4*(39*a^2*t^2-6*a*t^3+18*a+t^4+36*t) +
      9*(-13*a*t^2+28*t^3-6)*m, ?_⟩
  dsimp [t]; unfold H at *
  linear_combination -9*(-13*a*(n^4)^2 + 28*(n^4)^3 - 6)*hm

/-- Every integral solution on this plane is recovered by a divisor of
the displayed integer. The divisor also determines (a−n⁴)². -/
theorem plane_divisor_reduction (n x y z : ℤ)
    (hp : z+3*n^2*x+2*n^3*y = -n^6) (hs : z^2+y^2*z+x^3=2) :
    ∃ a m : ℤ, x=a-m ∧ z=n^2*m ∧ 2*n*y=2*m-3*a-n^4 ∧
      m*H a n=4*(2-a^3) ∧
      H a n ∣ 4*(n^24+540*n^12-108) ∧
      3*(a-n^4)^2=4*n^8-H a n := by
  let m := -(3*x+2*n*y+n^4)
  let a := x+m
  have hx : x=a-m := by dsimp [a]; ring
  have hz : z=n^2*m := by dsimp [m]; linear_combination hp
  have hy : 2*n*y=2*m-3*a-n^4 := by dsimp [a,m]; ring
  have h := plane_equation a m n y hy
  rw [← hx, ← hz] at h
  have hm : m*H a n=4*(2-a^3) := by linear_combination 4*hs-h
  exact ⟨a,m,hx,hz,hy,hm,plane_divisor a m n hm, by unfold H; ring⟩

end SmallCubic.TangentAtInfinity
