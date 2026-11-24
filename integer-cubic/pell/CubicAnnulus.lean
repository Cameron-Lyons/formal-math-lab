module

public import PellConstantFiber
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

public section
namespace SmallCubic
open Polynomial
variable {K : Type*} [Field K]

/-- Choose the second radius using the supported lower coefficients of the
reversed ordinate. At this radius a lower term or the denominator survives. -/
theorem choose_cubic_secondary_radius (h : ℚ) (hh : 0 < h) (S : Finset ℕ)
    (ord : ℕ → ℚ) (hs : ∀ i ∈ S, i < 3 ∧ 0 < ord i) :
    ∃ r : ℚ, 0 < r ∧ r ≤ h ∧ (∀ i ∈ S, 0 ≤ ord i + ((i : ℚ)-3)*r) ∧
      (r = h ∨ ∃ i ∈ S, ord i + ((i : ℚ)-3)*r = 0) := by
  classical
  let slope := fun (i : ℕ) => ord i/(3-(i : ℚ))
  let bounds := insert h (S.image slope)
  have hn : bounds.Nonempty := ⟨h, Finset.mem_insert_self ..⟩
  let r := bounds.min' hn
  have mem := Finset.min'_mem bounds hn
  have hd (i : ℕ) (hi : i ∈ S) : (0 : ℚ) < 3-i := by
    exact sub_pos.mpr (by exact_mod_cast (hs i hi).1)
  have hmem : r = h ∨ ∃ i ∈ S, slope i = r := by
    simpa [r, bounds] using mem
  refine ⟨r, ?_, Finset.min'_le _ _ (Finset.mem_insert_self ..), ?_, ?_⟩
  · rcases hmem with eq | ⟨i,hi,eq⟩
    · exact eq.symm ▸ hh
    · exact eq ▸ div_pos (hs i hi).2 (hd i hi)
  · intro i hi
    have le : r ≤ slope i := Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi))
    have mul := (le_div_iff₀ (hd i hi)).mp le
    linarith
  · rcases hmem with eq | ⟨i,hi,eq⟩
    · exact Or.inl eq
    · refine Or.inr ⟨i,hi,?_⟩
      have mul := (div_eq_iff (hd i hi).ne').mp eq
      linarith

private noncomputable abbrev embed := algebraMap K[X] (RatFunc K)

/-- At a radius strictly inside the denominator roots, the reduced cubic
identity forces every coefficient of the ordinate below degree three to vanish. -/
theorem cubic_inner_radius (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    {e : K} (he : e ≠ 0) {a b : K[X]}
    (hp : a^3 + C e*b^2 + (C e)^2*X^6 = 0) :
    ∃ k : K, b = C k*X^3 := by
  let t := (RatFunc.X : RatFunc K)
  have ht : t ≠ 0 := RatFunc.X_ne_zero
  have eq := congrArg (embed (K := K)) hp
  simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    map_zero] at eq
  have hc : RatFunc.C e*(embed b/t^3)^2 + RatFunc.C (1 : K)*(embed a/t^2)^3 =
      RatFunc.C (-(e^2)) := by
    simp only [map_one, one_mul, map_neg, map_pow]
    field_simp [ht]
    dsimp [t]
    linear_combination eq
  obtain ⟨⟨k,hk⟩,_⟩ := ratFunc_mordell_constants_over h₂ h₃ e 1 (-(e^2))
    he one_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ he)) _ _ hc
  refine ⟨k, RatFunc.algebraMap_injective K ?_⟩
  simpa [t] using (div_eq_iff (pow_ne_zero 3 ht)).mp hk

private theorem quad_ne_zero (c : K) :
    (RatFunc.X : RatFunc K)^2 - RatFunc.C c ≠ 0 := by
  intro h
  have hh : (X : K[X])^2 = C c := RatFunc.algebraMap_injective K (by simpa using sub_eq_zero.mp h)
  simpa using congrArg (fun p : K[X] => p.coeff 2) hh

/-- At the denominator radius the nonzero quadratic term makes any cubic ordinate impossible.
This statement permits every polynomial abscissa. -/
theorem cubic_denominator_radius (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    {e c b₀ b₁ b₂ b₃ : K} (he : e ≠ 0) (hc : c ≠ 0) (hb : b₃ ≠ 0) {a : K[X]}
    (hp : a^3 + C e*(C b₀+C b₁*X+C b₂*X^2+C b₃*X^3)^2 +
      (C e)^2*(X^2-C c)^3 = 0) : False := by
  let w := (RatFunc.X : RatFunc K)
  let c' := RatFunc.C c
  let s := (w^2+c')/(2*w)
  let d := (w^2-c')/(2*w)
  have hw : w ≠ 0 := RatFunc.X_ne_zero
  have h2 : (2 : RatFunc K) ≠ 0 := by
    rw [← map_ofNat RatFunc.C 2]
    exact (_root_.map_ne_zero RatFunc.C).mpr h₂
  have hd : d ≠ 0 := div_ne_zero (quad_ne_zero c) (mul_ne_zero h2 hw)
  have hd2 : s^2-c' = d^2 := by dsimp [s,d]; field_simp; ring
  let v := RatFunc.C b₀ + RatFunc.C b₁*s + RatFunc.C b₂*s^2 + RatFunc.C b₃*s^3
  have eq := congrArg (Polynomial.aeval s) hp
  simp only [map_add, map_mul, map_pow, map_sub, aeval_C, aeval_X, map_zero,
    RatFunc.algebraMap_eq_C] at eq
  change (Polynomial.aeval s a)^3 + RatFunc.C e*v^2 + (RatFunc.C e)^2*(s^2-c')^3 = 0 at eq
  rw [hd2] at eq
  have hh : RatFunc.C e*(v/d^3)^2 + RatFunc.C (1 : K)*(Polynomial.aeval s a/d^2)^3 =
      RatFunc.C (-(e^2)) := by
    simp only [map_one, one_mul, map_neg, map_pow]
    field_simp [hd]
    linear_combination eq
  obtain ⟨⟨k,hk⟩,_⟩ := ratFunc_mordell_constants_over h₂ h₃ e 1 (-(e^2))
    he one_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ he)) _ _ hh
  have hk' := (div_eq_iff (pow_ne_zero 3 hd)).mp hk
  dsimp [v,s,d] at hk'
  field_simp [hw,h2] at hk'
  have poly : C b₀*(2*X)^3 + C b₁*(X^2+C c)*(2*X)^2 +
      C b₂*(X^2+C c)^2*(2*X) + C b₃*(X^2+C c)^3 = C k*(X^2-C c)^3 := by
    apply RatFunc.algebraMap_injective K
    simp only [map_add, map_mul, map_pow, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      map_ofNat]
    dsimp [w,c'] at hk'
    linear_combination hk'
  have at0 := congrArg (Polynomial.eval 0) poly
  simp at at0
  have at6 := congrArg (fun p : K[X] => p.coeff 6) poly
  ring_nf at at6
  simp only [← C_pow, ← C_mul, coeff_add, coeff_sub, coeff_mul_C, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_mul_ofNat] at at6
  norm_num at at6
  have : (b₃ + k)*c^3 = 0 := by linear_combination at0
  have hneg : b₃ + k = 0 := (mul_eq_zero.mp this).resolve_right (pow_ne_zero 3 hc)
  have hz : (2 : K)*b₃ = 0 := by linear_combination hneg + at6
  exact hb ((mul_eq_zero.mp hz).resolve_left h₂)

attribute [local instance] Polynomial.algebra

/-- A polynomial whose cube has integral coefficients has integral coefficients
over an integrally closed base in the ambient field. -/
theorem lift_poly_of_cube {R F : Type*} [CommRing R] [Field F] [Algebra R F]
    [IsIntegrallyClosedIn R F] {a : F[X]} {rhs : R[X]}
    (h : rhs.map (algebraMap R F) = a^3) :
    ∃ A : R[X], A.map (algebraMap R F) = a := by
  have hc : IsIntegral R[X] (a^3) := by
    rw [← h]
    exact isIntegral_algebraMap (A := F[X]) (x := rhs)
  have ha : IsIntegral R[X] a := hc.of_pow (by decide : 0 < 3)
  apply (Polynomial.mem_lifts a).mp
  exact (Polynomial.lifts_iff_coeff_lifts a).mpr fun n =>
    IsIntegrallyClosedIn.isIntegral_iff.mp (ha.coeff n)

/-- A scaled reversed identity over a valuation ring (or any integrally closed
base in a field) is impossible as soon as either the quadratic denominator
coefficient or one of the three lower ordinate coefficients survives reduction. -/
theorem cubic_scaled_obstruction {R F : Type*} [CommRing R] [Field F] [Algebra R F]
    [IsIntegrallyClosedIn R F] (red : R →+* K)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    {a : F[X]} {B E : R[X]} {c l : R} {e b₀ b₁ b₂ b₃ : K}
    (hl : red l = 0) (he : e ≠ 0) (hb : b₃ ≠ 0) (hE : E.map red = C e)
    (hB : B.map red = C b₀+C b₁*X+C b₂*X^2+C b₃*X^3)
    (hit : red c ≠ 0 ∨ b₀ ≠ 0 ∨ b₁ ≠ 0 ∨ b₂ ≠ 0)
    (hp : (2*C l^12*(X^2-C c)^9 - E*B^2 - E^2*(X^2-C c)^3).map (algebraMap R F) = a^3) :
    False := by
  let rhs := 2*C l^12*(X^2-C c)^9 - E*B^2 - E^2*(X^2-C c)^3
  obtain ⟨A,hA⟩ := lift_poly_of_cube hp
  have hinj := (isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn R F)).1
  have hroot : rhs = A^3 := by
    apply Polynomial.map_injective _ hinj
    rw [Polynomial.map_pow, hA]
    exact hp
  have eq := congrArg (Polynomial.map red) hroot
  simp [rhs, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    hl, hE, hB] at eq
  have residual : (A.map red)^3 + C e*(C b₀+C b₁*X+C b₂*X^2+C b₃*X^3)^2 +
      (C e)^2*(X^2-C (red c))^3 = 0 := by linear_combination -eq
  by_cases hc : red c = 0
  · rw [hc, map_zero, sub_zero, ← pow_mul] at residual
    obtain ⟨k,hk⟩ := cubic_inner_radius h₂ h₃ he residual
    rcases hit with h | h | h | h
    · exact h hc
    · exact h (by simpa using congrArg (fun p : K[X] => p.coeff 0) hk)
    · exact h (by simpa [coeff_C_mul, coeff_X_pow, coeff_X] using congrArg (fun p : K[X] => p.coeff 1) hk)
    · exact h (by simpa [coeff_C_mul, coeff_X_pow] using congrArg (fun p : K[X] => p.coeff 2) hk)
  · exact cubic_denominator_radius h₂ h₃ he hc hb residual

end SmallCubic
