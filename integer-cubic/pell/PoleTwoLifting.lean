module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.Ring

public section

namespace SmallCubic
open MvPolynomial

variable {ι R k : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing k]

/-- A polynomial difference is the dot product with a row that reduces
to the gradient when its two inputs agree modulo the homomorphism. -/
private theorem polynomial_secant_row (ρ : R →+* k) (x y : ι → R)
    (hxy : ∀ j, ρ (x j) = ρ (y j)) (p : MvPolynomial ι R) :
    ∃ a : ι → R, eval x p - eval y p = ∑ i, a i * (x i - y i) ∧
      ∀ i, ρ (a i) = ρ (eval y (pderiv i p)) := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨a, ha, da⟩ := hp
    obtain ⟨b, hb, db⟩ := hq
    refine ⟨fun i => a i + b i, ?_, ?_⟩
    · simp only [map_add, add_mul, Finset.sum_add_distrib]
      rw [← ha, ← hb]
      ring
    · simp [da, db]
  | mul_X p j hp =>
    obtain ⟨a, ha, da⟩ := hp
    refine ⟨fun i => a i * x j + (if j = i then eval y p else 0), ?_, ?_⟩
    · simp only [map_mul, eval_X, add_mul, Finset.sum_add_distrib, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [show (∑ i, a i * x j * (x i-y i)) = (∑ i, a i * (x i-y i)) * x j by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring, ← ha]
      ring
    · intro i
      by_cases h : j = i
      · subst i
        simp [da, hxy]
        ring
      · simp [da, hxy, h]
        ring

/-- A square polynomial system over an integral domain has at most one
root in any residue class at which the reduced Jacobian is nonsingular.
The homomorphism may in particular be the residue map of a valuation ring. -/
theorem polynomial_system_lift_unique [NoZeroDivisors R]
    (ρ : R →+* k) (F : ι → MvPolynomial ι R) (x y : ι → R)
    (hxy : ∀ j, ρ (x j) = ρ (y j)) (hF : ∀ i, eval x (F i) = eval y (F i))
    (hJ : (Matrix.of fun i j => ρ (eval y (pderiv j (F i)))).det ≠ 0) : x = y := by
  choose row hrow hgradient using fun i => polynomial_secant_row ρ x y hxy (F i)
  let A : Matrix ι ι R := Matrix.of row
  have hA : A.det ≠ 0 := by
    intro h
    apply hJ
    have hm : ρ.mapMatrix A = Matrix.of fun i j => ρ (eval y (pderiv j (F i))) := by
      ext i j
      exact hgradient i j
    rw [← hm, ← ρ.map_det, h, map_zero]
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hA
  funext i
  change (∑ j, row i j * (x j-y j)) = 0
  rw [← hrow i, hF i, sub_self]

end SmallCubic
