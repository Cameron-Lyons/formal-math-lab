module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination

public section

namespace SmallCubic.QuinticFactor

/-- With z a factor of 2-r³, the square condition for a lift x=r+qz
has no denominator. This allows x to have pole order five. -/
theorem substitution {K : Type*} [CommRing K] (a r q z y : K)
    (h : a*z=2-r^3) :
    z^2+y^2*z+(r+q*z)^3-2 =
      z*(y^2-(a-z-3*r^2*q-3*r*q^2*z-q^3*z^2)) := by
  linear_combination h

/-- When q is minus a square the two leading terms of the required square
root leave a remainder of order at most four. -/
theorem negative_square_remainder {K : Type*} [CommRing K] (a r p z y : K)
    (h : y^2=a-z+3*r^2*p^2-3*r*p^4*z+p^6*z^2) :
    (2*y-2*p^3*z+3*r*p)*(2*y+2*p^3*z-3*r*p)=4*(a-z)+3*r^2*p^2 := by
  linear_combination 4*h

end SmallCubic.QuinticFactor
