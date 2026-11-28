module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! Boundary equation of an ordinary sextic substitution after a second
rescaling at 5. A surviving lower coefficient is impossible on every
nonconstant-x residue branch. -/
public section
namespace SmallCubic.SexticBoundary

open Polynomial

abbrev F := ZMod 5
abbrev K := QuadraticAlgebra F 2 0

private def rhs {R : Type*} [CommRing R] (a b u v w t : R) : R :=
  t^2 * (b*t+w)^4 - 4*(a*t^2+v*t+u)^3

private def overK (a b u v w : F) (t : K) : K :=
  rhs (algebraMap F K a) (algebraMap F K b) (algebraMap F K u)
    (algebraMap F K v) (algebraMap F K w) t

private def squareTest (r : F) : Prop := r^3=r
private instance (r : F) : Decidable (squareTest r) := inferInstanceAs (Decidable (r^3=r))

private theorem squares_pass (r : F) : squareTest (r^2) :=
  (by decide : ∀ r : F, squareTest (r^2)) r

set_option maxHeartbeats 0 in
private theorem finite_check (a b u v w : F) (ha : a=2 ∨ a=4) (hb : b≠0)
    (hf : ∀ t : F, squareTest (rhs a b u v w t))
    (h1 : squareTest ((overK a b u v w ⟨0,1⟩).norm))
    (h2 : squareTest ((overK a b u v w ⟨0,2⟩).norm)) :
    u=0 ∧ v=0 ∧ w=0 := by
  rcases ha with rfl | rfl <;> revert b u v w <;> decide +kernel

/-- The limiting quadratic and linear factors have no lower coefficients.
The hypothesis is a polynomial identity over the residue field. -/
theorem monomials_of_boundary_square (a b u v w : F) (e : F[X])
    (ha : a=2 ∨ a=4) (hb : b≠0)
    (h : e^2 = X^2*(C b*X+C w)^4 - 4*(C a*X^2+C v*X+C u)^3) :
    u=0 ∧ v=0 ∧ w=0 := by
  have atF (t : F) : (eval t e)^2 = rhs a b u v w t := by
    have he := congrArg (eval t) h
    simpa [rhs] using he
  have atK (t : K) : (eval₂RingHom (algebraMap F K) t e)^2 = overK a b u v w t := by
    have he := congrArg (eval₂RingHom (algebraMap F K) t) h
    simpa [overK, rhs, eval₂_pow, eval₂_mul] using he
  have hn (t : K) : squareTest ((overK a b u v w t).norm) := by
    rw [← atK, map_pow]
    exact squares_pass _
  exact finite_check a b u v w ha hb (fun t => by rw [← atF]; exact squares_pass _) (hn _) (hn _)

end SmallCubic.SexticBoundary
