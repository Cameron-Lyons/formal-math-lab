module

public import SmallCubic
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section

namespace SmallCubic.SecantOrbit

/-- The norm used in the final tangent test, with the Vieta relations
for the three roots of the monic cubic associated to the binary form. -/
theorem binary_cubic_norm {K : Type*} [CommRing K] (a b c d m n r s t : K)
    (h₁ : r+s+t = -b) (h₂ : r*s+s*t+t*r = a*c) (h₃ : r*s*t = -a^2*d) :
    (a*m-r*n)*(a*m-s*n)*(a*m-t*n) =
      a^2*(a*m^3+b*m^2*n+c*m*n^2+d*n^3) := by
  linear_combination -(a*m)^2*n*h₁ + a*m*n^2*h₂ - n^3*h₃

/-- At a split prime the three reductions of an element of the form
a - b θ satisfy this necessary linear relation. -/
theorem split_norm_relation {K : Type*} [CommRing K] (a b r s t : K) :
    (s-t)*(a-b*r)+(t-r)*(a-b*s)+(r-s)*(a-b*t)=0 := by ring

/-- The homogeneous part of the cubic vanishes in every direction
(-a²b,a³,b³). The restriction to such a line is quadratic. -/
theorem line_at_infinity {K : Type*} [CommRing K] (x y z a b t : K) :
    (z + t*b^3)^2 + (y + t*a^3)^2*(z + t*b^3) + (x - t*a^2*b)^3 -
      (z^2+y^2*z+x^3) =
    t * ((2*z+y^2)*b^3-3*x^2*a^2*b+2*y*z*a^3 +
      t*(b^6+2*y*a^3*b^3+3*x*a^4*b^2+z*a^6)) := by ring

/-- Third intersections on the tangent plane use a cubic and a quadratic
in the direction (i,j,k), both homogeneous. -/
theorem tangent_line {K : Type*} [CommRing K] (x y z i j k t : K)
    (h : 3*x^2*i+2*y*z*j+(y^2+2*z)*k=0) :
    (z+t*k)^2+(y+t*j)^2*(z+t*k)+(x+t*i)^3-(z^2+y^2*z+x^3) =
    t^2*(3*x*i^2+2*y*j*k+z*j^2+k^2+t*(i^3+j^2*k)) := by
  linear_combination t*h

/-- A secant through the affine seed (0,1,1) and any rational point at
infinity cannot give a second integer point with changed abscissa. -/
theorem seed_secant (a b t : ℤ) (hab : IsCoprime a b)
    (hs : Solves (-t*a^2*b) (1+t*a^3) (1+t*b^3)) : t*a^2*b=0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · ring
  let s := a^3+b^3
  have hz : t*(2*a^3+3*b^3+t*s^2)=0 := by
    dsimp [s]
    have hdisc := (solves_iff_discriminant ..).mp hs
    nlinarith only [hdisc]
  have h : 2*a^3+3*b^3+t*s^2=0 := (mul_eq_zero.mp hz).resolve_left ht
  have hdA : s ∣ a^3 := by
    refine ⟨3+t*s, ?_⟩
    dsimp [s] at h ⊢
    linear_combination -h
  have hdB : s ∣ b^3 := by
    refine ⟨-2-t*s, ?_⟩
    dsimp [s] at h ⊢
    linear_combination h
  have hu : IsUnit s := (show IsCoprime (a^3) (b^3) from hab.pow).isUnit_of_dvd' hdA hdB
  have hf : s = (a+b)*(a^2-a*b+b^2) := by dsimp [s]; ring
  rw [hf, (Commute.all _ _).isUnit_mul_iff] at hu
  have h1 : (a+b)^2=1 := by
    rcases Int.isUnit_iff.mp hu.1 with h | h <;> rw [h] <;> norm_num
  have h2 : a^2-a*b+b^2=1 ∨ a^2-a*b+b^2 = -1 := Int.isUnit_iff.mp hu.2
  have h3 : 3*(a*b)=0 ∨ 3*(a*b)=2 := by
    rcases h2 with h | h
    · left; linear_combination h1-h
    · right; linear_combination h1-h
  have h4 : a*b=0 := by omega
  rcases mul_eq_zero.mp h4 with rfl | rfl <;> simp

/-- The leading coefficient and the nonconstant factor in the discriminant
of the tangent-plane direction cubic are nonzero at every integral point. -/
theorem tangent_discriminant_nonzero (x y z : ℤ) (hs : Solves x y z) :
    y^2+2*z ≠ 0 ∧ x^6-(y^2+2*z)*y^2*z^2 ≠ 0 := by
  have hc : x^3=2-z^2-y^2*z := by nlinarith only [(solves_iff_discriminant ..).mp hs]
  constructor
  · intro h
    have hh := congrArg (fun t : ℤ => (t : ZMod 4)) h
    have hx := congrArg (fun t : ℤ => (t : ZMod 4)) hc
    push_cast at hh hx
    exact (by decide : ∀ x y z : ZMod 4,
      y^2+2*z=0 → x^3=2-z^2-y^2*z → False) _ _ _ hh hx
  · have hr : x^6-(y^2+2*z)*y^2*z^2 = (z^2-2)^2-4*y^2*z := by
      rw [show x^6=(x^3)^2 by ring, hc]; ring
    rw [hr]
    intro h
    have hh := congrArg (fun t : ℤ => (t : ZMod 8)) h
    push_cast at hh
    exact (by decide : ∀ y z : ZMod 8, (z^2-2)^2-4*y^2*z ≠ 0) _ _ hh

/-- The tangent plane through an integral point has three distinct directions
at infinity over an algebraic closure. In the rational boundary coordinate,
its cubic never shares a root with its derivative. -/
theorem tangent_no_double_root {K : Type*} [Field K] [CharZero K]
    (x y z : ℤ) (hs : Solves x y z) (t : K) :
    ¬ (((y:K)^2+2*z)*t^3 - 3*(x:K)^2*t + 2*y*z = 0 ∧
       3*((y:K)^2+2*z)*t^2 - 3*(x:K)^2 = 0) := by
  rintro ⟨hf,hd⟩
  let c : K := (y:K)^2+2*z
  have hx : (x:K)^2 = c*t^2 := by dsimp [c]; linear_combination -(1/3 : K)*hd
  have ht : c*t^3 = (y:K)*z := by
    dsimp [c]; linear_combination -(1/2 : K)*hf+(t/2)*hd
  have he : (x:K)^6 - ((y:K)^2+2*z)*(y:K)^2*(z:K)^2 = 0 := by
    change (x:K)^6-c*(y:K)^2*(z:K)^2=0
    rw [show (x:K)^6=((x:K)^2)^3 by ring, hx,
        show c*(y:K)^2*(z:K)^2=c*((y:K)*z)^2 by ring, ← ht]
    ring
  exact (tangent_discriminant_nonzero x y z hs).2 (by exact_mod_cast he)

end SmallCubic.SecantOrbit
