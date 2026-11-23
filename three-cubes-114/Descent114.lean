import Lean

namespace ThreeCubes114

/-- Fixing the signed sum `a = x + y` maps a putative solution to an affine
integral point `(X,Y)` on a Mordell curve, with `X = -12*a*z` and
`Y = 36*a²*(x-y)`. The identity also holds for general `k`. -/
theorem mordell_fiber (x y z k a : Int) (ha : a = x+y)
    (h : x^3 + y^3 + z^3 = k) :
    (36*a^2*(x-y))^2 = (-12*a*z)^3 + 432*a^3*(4*k-a^3) := by
  subst a k
  grind

/-- A proof excluding *all* affine integral points on one Mordell curve
therefore excludes that signed sum, for arbitrarily large `z`. -/
theorem exclude_empty_fiber (a : Int)
    (empty : ∀ X Y : Int, Y^2 ≠ X^3 + 432*a^3*(456-a^3)) :
    ∀ x y z : Int, x+y = a → x^3 + y^3 + z^3 ≠ 114 := by
  intro x y z ha h
  exact empty _ _ (mordell_fiber x y z 114 a ha.symm h)

/-- One of the globally excluded pair sums passes the ordinary cube-root test. -/
example : (2755 : Int)^3 % 20381 = 114 := by decide

/-- Factoring a large cube out of the curve coefficient made 2-descent feasible
for these larger fibers. Each also passes the ordinary cube-root test. -/
example : (456 - (-315859094 : Int)^3) % (1013^3) = 0 ∧
    (46867184 : Int)^3 % 315859094 = 114 := by decide

example : (456 - (10208993386 : Int)^3) % (3385^3) = 0 ∧
    (7922153720 : Int)^3 % 10208993386 = 114 := by decide

example : (456 - (4053332798386 : Int)^3) % (404245^3) = 0 ∧
    (3994532349050 : Int)^3 % 4053332798386 = 114 := by decide

end ThreeCubes114
