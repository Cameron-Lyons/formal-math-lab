module

public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith

public section
namespace SmallCubic
open Polynomial

private theorem three_dvd_of_cube_ratio {u v : ℚ} {n : ℕ} (hv : v ≠ 0)
    (h : u ^ 3 = 2 ^ n * v ^ 3) : 3 ∣ n := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp [hv] at h
  have ht : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide : 1 < 2)
  have H := congrArg (padicValRat 2) h
  rw [padicValRat.mul (by positivity : (2 : ℚ) ^ n ≠ 0) (pow_ne_zero _ hv),
    padicValRat.pow, padicValRat.pow, padicValRat.pow, ht, mul_one] at H
  omega

/-- Every polynomial divisor of 2L³ − X³ coprime to L has degree divisible by three.
The determinant norm on the quotient by the divisor turns the identity into one over ℚ. -/
theorem three_dvd_degree_of_cube_factor {A L X : ℚ[X]}
    (hc : IsCoprime L A) (hd : A ∣ 2 * L ^ 3 - X ^ 3) : 3 ∣ A.natDegree := by
  let q := AdjoinRoot.mk A
  let N := Algebra.norm ℚ (S := AdjoinRoot A)
  have H := AdjoinRoot.mk_eq_zero.mpr hd
  change q (2 * L ^ 3 - X ^ 3) = 0 at H
  rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, sub_eq_zero] at H
  have h := congrArg N H.symm
  rw [map_pow, map_mul, map_pow] at h
  have hN : N 2 = (2 : ℚ) ^ A.natDegree := by
    change Algebra.norm ℚ (↑(2 : ℕ) : AdjoinRoot A) = _
    rw [Algebra.norm_natCast]
    change (2 : ℚ) ^ Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {A}) = _
    rw [finrank_quotient_span_eq_natDegree]
  rw [hN] at h
  apply three_dvd_of_cube_ratio _ h
  obtain ⟨a, b, hab⟩ := hc
  have he := congrArg q hab
  simp only [map_add, map_mul, map_one, show q A = 0 from AdjoinRoot.mk_self,
    mul_zero, add_zero] at he
  have hn := congrArg N he
  rw [map_mul, map_one] at hn
  intro hz
  simp [hz] at hn

/-- At t = ∞ the leading coefficients cannot cancel, since 2 is not a rational cube. -/
theorem cube_difference_degree_of_le {X L : ℚ[X]} (hL : L ≠ 0)
    (hX : X.natDegree ≤ L.natDegree) :
    (2 * L ^ 3 - X ^ 3).natDegree = 3 * L.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply (natDegree_sub_le _ _).trans
    apply max_le
    · rw [← C_ofNat (R := ℚ) 2, natDegree_C_mul (by decide : (2 : ℚ) ≠ 0), natDegree_pow]
    · rw [natDegree_pow]; omega
  · rw [← C_ofNat (R := ℚ) 2, coeff_sub, coeff_C_mul,
      coeff_pow_mul_natDegree, coeff_pow_of_natDegree_le hX]
    intro hz
    have := three_dvd_of_cube_ratio (n := 1) (leadingCoeff_ne_zero.mpr hL)
      (show (X.coeff L.natDegree) ^ 3 = 2 ^ 1 * L.leadingCoeff ^ 3 by linarith)
    omega

end SmallCubic
