module

public import PellConstantFiber
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Polynomial graphs x=f(y) on the cubic surface. -/
public section
namespace SmallCubic.PolynomialGraph
open Polynomial

/-- A square times a polynomial of degree at most two can occur only for
a graph of degree at most eight. This holds before imposing integrality. -/
theorem degree_bound (f q e : ℚ[X]) (hq : q.natDegree ≤ 2)
    (h : X^4 + C 8 = 4*f^3 + q*e^2) : f.natDegree ≤ 8 := by
  by_contra! hn
  let H : ℚ[X] := X^4+C 8
  have dH : H.natDegree = 4 := natDegree_X_pow_add_C
  have lcH : H.leadingCoeff = 1 := leadingCoeff_X_pow_add_C (by decide)
  have hf : f ≠ 0 := by intro h; simp [h] at hn
  have hH : H = 4*f^3 + q*e^2 := h
  have hd := congrArg derivative hH
  simp only [derivative_add, derivative_mul, derivative_ofNat, zero_mul, zero_add,
    derivative_pow] at hd
  norm_num at hd
  change H.derivative = 4*(3*f^2*f.derivative) + (q.derivative*e^2+q*(2*e*e.derivative)) at hd
  let N := 3*H*f.derivative-H.derivative*f
  have hdvd : e ∣ N := by
    refine ⟨3*q*e*f.derivative-q.derivative*e*f-2*q*f*e.derivative, ?_⟩
    dsimp [N]
    linear_combination 3*f.derivative*hH - f*hd
  have hN : N ≠ 0 := by
    intro hz
    have heq : 3*H*f.derivative = H.derivative*f := sub_eq_zero.mp hz
    have lc := congrArg leadingCoeff heq
    simp only [leadingCoeff_mul, leadingCoeff_derivative, lcH, dH, Nat.cast_ofNat, one_mul] at lc
    have lc3 : (3 : ℚ[X]).leadingCoeff = 3 := leadingCoeff_C (3:ℚ)
    rw [lc3] at lc
    have hc : (3*(f.natDegree:ℚ)-4)*f.leadingCoeff=0 := by linear_combination lc
    have := (mul_eq_zero.mp hc).resolve_right (leadingCoeff_ne_zero.mpr hf)
    have : (8:ℚ) < f.natDegree := by exact_mod_cast hn
    linarith
  have dN : N.natDegree ≤ f.natDegree+3 := by
    apply (natDegree_sub_le _ _).trans (max_le _ _)
    · apply natDegree_mul_le.trans
      have h3 : (3 : ℚ[X]).natDegree = 0 := natDegree_C (3:ℚ)
      have hleft := natDegree_mul_le (p := (3 : ℚ[X])) (q := H)
      have hright := natDegree_derivative_le f
      omega
    · apply natDegree_mul_le.trans
      have hleft := natDegree_derivative_le H
      omega
  have hde := (natDegree_le_of_dvd hdvd hN).trans dN
  have heq : 4*f^3-H = -(q*e^2) := by linear_combination -hH
  have d4 : (4*f^3).natDegree=3*f.natDegree := by
    change (C (4:ℚ)*f^3).natDegree=_
    rw [natDegree_C_mul (by decide),natDegree_pow]
  have dprod := natDegree_mul_le (p:=q) (q:=e^2)
  rw [natDegree_pow] at dprod
  have dh := congrArg natDegree heq
  rw [natDegree_sub_eq_left_of_natDegree_lt (by omega), d4, natDegree_neg] at dh
  omega

variable {K : Type*} [Field K]
private noncomputable abbrev emb := algebraMap K[X] (RatFunc K)

/-- A zoom at which the right-hand side becomes constant forces the reduced
abscissa to be constant too. -/
theorem inner_reduction (h₂ : (2:K) ≠ 0) (h₃ : (3:K) ≠ 0)
    (k m : K) (hk : k ≠ 0) (hm : m ≠ 0) (a b : K[X])
    (h : C k*b^2+4*a^3=C m) : ∃ c : K, a = C c := by
  have h4 : (4:K) ≠ 0 := by rw [show (4:K)=2*2 by ring]; exact mul_ne_zero h₂ h₂
  have he := congrArg (emb (K := K)) h
  simp only [map_add,map_mul,map_pow,map_ofNat,RatFunc.algebraMap_C] at he
  obtain ⟨_,c,hc⟩ := ratFunc_mordell_constants_over h₂ h₃ k 4 m hk h4 hm
    (emb b) (emb a) (by simpa only [map_ofNat] using he)
  exact ⟨c, RatFunc.algebraMap_injective K (by simpa using hc)⟩

/-- A zoom at a growing radius would require a polynomial in T³ to be a
nonzero scalar times T⁴. This rules out transitions from degree one to a
higher degree at infinity. -/
theorem outer_reduction (h₂ : (2:K) ≠ 0) (h₃ : (3:K) ≠ 0)
    (k : K) (hk : k ≠ 0) (a b : K[X])
    (h : C k*b^2+4*a^3=X^4) : a = 0 := by
  let u := (RatFunc.X : RatFunc K)
  have hu : u ≠ 0 := RatFunc.X_ne_zero
  let A := a.comp (X^3)
  let B := b.comp (X^3)
  have hpoly : C k*B^2+4*A^3 = X^12 := by
    have he := congrArg (fun p : K[X] => p.comp (X^3)) h
    simpa [A,B,add_comp,mul_comp,pow_comp,← pow_mul] using he
  have he := congrArg (emb (K := K)) hpoly
  simp only [map_add,map_mul,map_pow,map_ofNat,RatFunc.algebraMap_X,RatFunc.algebraMap_C] at he
  have h4 : (4:K) ≠ 0 := by rw [show (4:K)=2*2 by ring]; exact mul_ne_zero h₂ h₂
  obtain ⟨_,c,hc⟩ := ratFunc_mordell_constants_over h₂ h₃ k 4 1 hk h4 one_ne_zero
    (emb B/u^6) (emb A/u^4) (by
      simp only [map_ofNat,map_one]
      field_simp [hu]
      dsimp [u]
      linear_combination he)
  by_contra ha
  have hA : A = C c * X^4 := RatFunc.algebraMap_injective K (by
    simpa [u] using (div_eq_iff (pow_ne_zero 4 hu)).mp hc)
  have hn : A ≠ 0 := by
    simp [A, comp_eq_zero_iff, ha]
  have hc0 : c ≠ 0 := by intro h; simp [h] at hA; exact hn hA
  have de := congrArg natDegree hA
  simp [A,natDegree_comp,natDegree_C_mul hc0] at de
  omega

end SmallCubic.PolynomialGraph
