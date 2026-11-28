module

public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

public section
namespace SmallCubic.TwoPoint
open Polynomial
open scoped Polynomial

/-- Over any nontrivial commutative ring, the polynomials of degree at most
`d` taking `a` and `b` at 0 and 1 have the bounded normal form used by the
modulo-4096 certificate. This also applies to rings with zero divisors. -/
theorem marked_polynomial_iff {K : Type*} [CommRing K] [Nontrivial K]
    (P : K[X]) (a b : K) {d : ℕ} (hd : 2 ≤ d) (hp : P.natDegree ≤ d) :
    (P.eval 0 = a ∧ P.eval 1 = b) ↔
      ∃ R : K[X], R.natDegree ≤ d-2 ∧
        P = C a + C (b-a)*X + X*(X-1)*R := by
  constructor
  · rintro ⟨h₀,h₁⟩
    let L : K[X] := C a + C (b-a)*X
    have hl : L.natDegree ≤ d := by
      apply natDegree_add_le_of_degree_le
      · simp
      · exact (natDegree_C_mul_le ..).trans (natDegree_X_le.trans (by omega))
    have hz : X ∣ P-L := by
      apply X_dvd_iff.mpr
      rw [coeff_zero_eq_eval_zero]
      simp [L,h₀]
    obtain ⟨Q,hQ⟩ := hz
    have hq1 : Q.eval 1 = 0 := by
      have he := congrArg (fun f : K[X] => f.eval 1) hQ
      simpa [L, h₁] using he.symm
    have hq : (X-1 : K[X]) ∣ Q := by
      simpa using (dvd_iff_isRoot.mpr (show IsRoot Q 1 from hq1))
    obtain ⟨R,hR⟩ := hq
    have hs : P-L = X*(X-1)*R := by rw [hQ,hR,mul_assoc]
    refine ⟨R, ?_, ?_⟩
    · by_cases hr : R = 0
      · simp [hr]
      have hm : Monic (X*(X-1) : K[X]) := monic_X.mul (by simpa using monic_X_sub_C (1 : K))
      have hdeg := (natDegree_sub_le P L).trans (max_le hp hl)
      rw [hs, hm.natDegree_mul' hr] at hdeg
      have htwo : (X*(X-1) : K[X]).natDegree = 2 := by
        rw [monic_X.natDegree_mul' (by simpa using X_sub_C_ne_zero (1 : K))]
        have h1 : (X-1 : K[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : K)
        simp [h1]
      omega
    · exact (sub_eq_iff_eq_add.mp hs).trans (add_comm _ _)
  · rintro ⟨R,_,rfl⟩
    simp

/-- The quadratic reduction used in the integral Pell-coordinate ring. -/
theorem marked_coordinate_square {K : Type*} [CommRing K] {u v : K}
    (h : u^2-3*v^2 = 1) :
    (u-1-v)^2 = 2*(v^2-v) - 2*(1+v)*(u-1-v) := by
  linear_combination h

/-- Multiplication of polynomial pairs in the integral-coordinate certificate. -/
theorem marked_pair_mul {K : Type*} [CommRing K] {v w : K}
    (hw : w^2 = 2*(v^2-v) - 2*(1+v)*w) (p q r s : K) :
    (p+w*q)*(r+w*s) = p*r + 2*(v^2-v)*(q*s) + w*(p*s+r*q-2*(1+v)*(q*s)) := by
  linear_combination q*s*hw

end SmallCubic.TwoPoint
