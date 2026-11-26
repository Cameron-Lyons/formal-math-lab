module

public import Equation17260
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Tactic.Abel

@[expose] public section

namespace Equation17260

/-- The coefficient equations of an affine model force the coefficient semiring to be trivial. -/
theorem affine_coefficients_trivial {R : Type*} [Semiring R] (A B : R)
    (hAA : A * A = 0)
    (hAB : A * B + B * B * A = 1)
    (hBA : B * A + B * B * B * A + B * B * B * B = 0) : (1 : R) = 0 := by
  have cancelB (v : R) (hv : B * v = 0) : v = 0 := by
    -- The second coefficient identity recovers `v` from `A * v`.
    have hrep : B * (B * (A * v)) = v := by
      simpa only [add_mul, mul_assoc, hv, mul_zero, zero_add, one_mul]
        using congrArg (fun t => t * v) hAB
    -- The third identity then forces that recovered value to be zero.
    have hav : B * (A * v) = 0 := by
      simpa only [add_mul, mul_assoc, hrep, hv, mul_zero, add_zero, zero_mul]
        using congrArg (fun t => t * v) hBA
    calc
      v = B * (B * (A * v)) := hrep.symm
      _ = 0 := by rw [hav, mul_zero]
  have hfourA : B * (B * (B * (B * A))) = 0 := by
    have hh := congrArg (fun t => t * A) hBA
    simpa only [add_mul, mul_assoc, hAA, mul_zero, zero_add, zero_mul] using hh
  have hA : A = 0 := cancelB A (cancelB (B * A)
    (cancelB (B * (B * A)) (cancelB (B * (B * (B * A))) hfourA)))
  simpa only [hA, zero_mul, mul_zero, add_zero] using hAB.symm


/-- An affine operation with arbitrary additive endomorphisms and a constant. -/
def affineOp {G : Type*} [AddCommMonoid G] (A B : AddMonoid.End G) (c : G) : G → G → G :=
  fun x y => A x + B y + c

private theorem affine_expand {G : Type*} [AddCommMonoid G]
    (A B : AddMonoid.End G) (c x y z : G) :
    affineOp A B c (affineOp A B c y x)
      (affineOp A B c z (affineOp A B c x (affineOp A B c z z))) =
      (A * A) y + (A * B + B * B * A) x +
      (B * A + B * B * B * A + B * B * B * B) z +
      (A c + B (B (B c)) + B (B c) + B c + c) := by
  change _ = A (A y) + (A (B x) + B (B (A x))) +
    (B (A z) + B (B (B (A z))) + B (B (B (B z)))) +
    (A c + B (B (B c)) + B (B c) + B c + c)
  simp only [affineOp, map_add]
  abel

/-- No nontrivial commutative additive monoid admits an affine operation satisfying Equation 17260.
No finiteness assumption is needed. -/
theorem affine_subsingleton {G : Type*} [AddCommMonoid G]
    (A B : AddMonoid.End G) (c : G) (h : Law (affineOp A B c)) : Subsingleton G := by
  have heq (x y z : G) : x =
      (A * A) y + (A * B + B * B * A) x +
      (B * A + B * B * B * A + B * B * B * B) z +
      (A c + B (B (B c)) + B (B c) + B c + c) :=
    (h x y z).trans (affine_expand A B c x y z)
  have hc : A c + B (B (B c)) + B (B c) + B c + c = 0 := by
    simpa only [map_zero, zero_add] using (heq 0 0 0).symm
  have hAA : A * A = 0 := by
    ext v
    simpa only [map_zero, zero_add, add_zero, hc, AddMonoid.End.zero_apply]
      using (heq 0 v 0).symm
  have hAB : A * B + B * B * A = 1 := by
    ext v
    simpa only [map_zero, zero_add, add_zero, hc, AddMonoid.End.one_apply]
      using (heq v 0 0).symm
  have hBA : B * A + B * B * B * A + B * B * B * B = 0 := by
    ext v
    simpa only [map_zero, zero_add, add_zero, hc, AddMonoid.End.zero_apply]
      using (heq 0 0 v).symm
  have h10 := affine_coefficients_trivial A B hAA hAB hBA
  have hz (v : G) : v = 0 := by
    have hh := congrArg (fun f : AddMonoid.End G => f v) h10
    simpa only [AddMonoid.End.one_apply, AddMonoid.End.zero_apply] using hh
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end Equation17260
