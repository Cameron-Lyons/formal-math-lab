module

public import CubicAnnulus
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

public section
namespace SmallCubic
open Polynomial
variable {K : Type*} [Field K]

/-- The doubled parameter makes the reduced ordinate even. The constant-fiber
theorem forces it to be a multiple of the odd monomial X³, hence zero. -/
theorem cubic_simple_pole (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    {e k : K} (he : e ≠ 0) (hk : k ≠ 0) {a b : K[X]}
    (hp : a^3 + C e*b^2 + (C e)^2*(C k*X)^3 = 0) : b = 0 := by
  let lin := C k⁻¹*X
  have sc : C k*lin = X := by dsimp [lin]; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hk, map_one, one_mul]
  have hs := congrArg (fun f : K[X] => f.comp lin) hp
  simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp, zero_comp, sc] at hs
  have hsq := congrArg (expand K 2) hs
  simp only [map_add, map_mul, map_pow, expand_C, expand_X, map_zero, ← pow_mul] at hsq
  obtain ⟨v,hv⟩ := cubic_inner_radius h₂ h₃ he hsq
  have h3 := congrArg (fun f : K[X] => f.coeff 3) hv
  have vz : v = 0 := by
    simpa [coeff_expand (by decide : 0 < 2)] using h3.symm
  rw [vz, map_zero, zero_mul] at hv
  have bz := (expand_eq_zero (by decide : 0 < 2)).mp hv
  exact (comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero hk))).mp bz

/-- Specialization at a lifted simple denominator root. The rescaled ordinate
must be zero modulo the maximal ideal. -/
theorem cubic_scaled_simple_pole {R F : Type*} [CommRing R] [Field F] [Algebra R F]
    [IsIntegrallyClosedIn R F] (red : R →+* K)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    {a : F[X]} {B E L : R[X]} {l : R} {e k : K}
    (hl : red l = 0) (he : e ≠ 0) (hk : k ≠ 0) (hE : E.map red = C e)
    (hL : L.map red = C k*X)
    (hp : (2*C l^12*L^9 - E*B^2 - E^2*L^3).map (algebraMap R F) = a^3) :
    B.map red = 0 := by
  obtain ⟨A,hA⟩ := lift_poly_of_cube hp
  have hinj := (isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn R F)).1
  have hroot : 2*C l^12*L^9 - E*B^2 - E^2*L^3 = A^3 := by
    apply Polynomial.map_injective _ hinj
    rw [Polynomial.map_pow, hA]
    exact hp
  have eq := congrArg (Polynomial.map red) hroot
  simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, hl, hE, hL] at eq
  apply cubic_simple_pole h₂ h₃ he hk (a := A.map red)
  linear_combination -eq

namespace Split13
noncomputable def y₁ : (ZMod 13)[X] :=
  1+3*X+10*X^2+8*X^3+4*X^4+X^5+X^6
noncomputable def z₁ : (ZMod 13)[X] :=
  1+11*X+4*X^2+7*X^3+9*X^4+10*X^5+2*X^6
noncomputable def y₂ : (ZMod 13)[X] :=
  1+3*X+7*X^2+4*X^3+7*X^4+X^5+2*X^6
noncomputable def z₂ : (ZMod 13)[X] :=
  1+11*X+6*X^2+6*X^3+5*X^4+8*X^5+X^6

/-- Both normalized split residue classes through (0,1,1) meet the local
criterion at the simple denominator root −3. -/
theorem split13_residue_values :
    y₁.eval (-3) = 0 ∧ y₁.derivative.eval (-3) = 0 ∧ z₁.eval (-3) = 1 ∧
    y₂.eval (-3) = 0 ∧ y₂.derivative.eval (-3) = 0 ∧ z₂.eval (-3) = 12 := by
  norm_num [y₁,y₂,z₁,z₂,derivative_add,derivative_mul,derivative_X_pow]; decide

end Split13
end SmallCubic
