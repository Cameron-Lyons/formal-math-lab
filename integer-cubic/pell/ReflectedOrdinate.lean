module

public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

public section

namespace SmallCubic.ReflectedOrdinate

abbrev F := ZMod 7
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

set_option maxHeartbeats 0 in
/-- Coefficients of degrees four down to zero in
4(L*T²+a)^3 - (2*T³+d*T+c)^2 = (l*T+m)^4 + 8*r^12.
The leading terms cancel when L is one of 1, 2, 4. -/
theorem quadratic_boundary :
    ∀ L : F, (L=1 ∨ L=2 ∨ L=4) →
    ∀ a l d : F, 12*L^2*a-4*d=l^4 →
    ∀ m c : F, -4*c=4*l^3*m →
    12*L*a^2-d^2=6*l^2*m^2 → -2*d*c=4*l*m^3 →
    ∀ r : F, 4*a^3-c^2=m^4+8*r^12 →
    a=0 ∧ l=0 ∧ d=0 ∧ m=0 ∧ c=0 ∧ r=0 := by
  decide +kernel

/-- The next boundary has reversed abscissa with a simple zero.
The coefficients of degrees two, one and zero suffice. -/
theorem linear_boundary :
    ∀ v : F, v ≠ 0 → ∀ c q : F,
    2*v*c+q*v^2=0 → c^2+2*v*c*q=0 →
    ∀ d r : F, q*c^2=d^4+8*r^12 →
    c=0 ∧ q=0 ∧ d=0 ∧ r=0 := by
  decide +kernel

/-- A linear quotient coordinate s and its conjugate r on the Pell conic. -/
theorem conic_coordinates {D u v : ℚ} (a b : ℚ) (h : u^2-D*v^2=1) :
    (b*u+D*a*v)^2 = b^2 + 2*D*a*(a*(u-1)+b*v) + D*(a*(u-1)+b*v)^2 := by
  linear_combination (b^2-D*a^2)*h

end SmallCubic.ReflectedOrdinate

namespace SmallCubic.ReflectedFactor

/-- Multiplication by 1 + 2√k sends the unit Pell conic to the pointed
quadratic r² = 1 + s + ks². The unit (1,0) maps to (0,1). -/
theorem pell_to_quadratic {k u v : ℚ} (hk : k ≠ 0) (h : u^2-k*v^2=1) :
    let s := (u+2*k*v-1)/(2*k)
    let r := u+v/2
    r^2=1+s+k*s^2 := by
  dsimp
  field_simp
  linear_combination (4*k-1)*h

/-- A rational identity in the reflected-factor family gives the desired
cubic identity at every rational point of the unit Pell conic. -/
theorem reflected_substitution {k u v : ℚ} (hk : k ≠ 0) (h : u^2-k*v^2=1)
    (X E Z : ℚ → ℚ)
    (identity : ∀ s, X s ^ 3 + Z s ^ 2 + (1+s+k*s^2)*E s^2*Z s=2) :
    let s := (u+2*k*v-1)/(2*k)
    let r := u+v/2
    (Z s)^2 + (r*E s)^2*Z s + (X s)^3=2 := by
  intro s r
  rw [mul_pow, show r^2=1+s+k*s^2 from pell_to_quadratic hk h]
  linear_combination identity s

end SmallCubic.ReflectedFactor
