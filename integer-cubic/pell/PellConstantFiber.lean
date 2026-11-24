module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.FLT.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section
namespace SmallCubic
open Polynomial

private noncomputable abbrev emb {K : Type*} [Field K] := algebraMap K[X] (RatFunc K)

/-- A rational function with a constant positive power is constant. -/
theorem ratFunc_constant_of_pow {K : Type*} [Field K] {f : RatFunc K} {c : K} {n : ℕ} (hn : 0 < n)
    (h : f^n = RatFunc.C c) : ∃ a : K, f = RatFunc.C a := by
  by_contra nc
  apply f.transcendental_of_ne_C nc
  refine ⟨X^n-C c, X_pow_sub_C_ne_zero hn c, ?_⟩
  simp [RatFunc.algebraMap_eq_C, h]

/-- A nonsingular equation kA² + lB³ = m has only constant rational-function solutions in characteristic different from 2 and 3.
Its reduced denominators have the form s³ and s². Clearing them gives the
polynomial Fermat–Catalan equation of signature (2,6,3). -/
theorem ratFunc_mordell_constants_over {K : Type*} [Field K]
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (k l m : K) (hk : k ≠ 0) (hl : l ≠ 0) (hm : m ≠ 0)
    (A B : RatFunc K) (h : RatFunc.C k*A^2 + RatFunc.C l*B^3 = RatFunc.C m) :
    (∃ a : K, A = RatFunc.C a) ∧ (∃ b : K, B = RatFunc.C b) := by
  have k' : RatFunc.C k ≠ 0 := (_root_.map_ne_zero RatFunc.C).mpr hk
  have l' : RatFunc.C l ≠ 0 := (_root_.map_ne_zero RatFunc.C).mpr hl
  by_cases a0 : A = 0
  · subst A
    refine ⟨⟨0, by simp⟩, ratFunc_constant_of_pow (n := 3) (c := m/l) (by decide) ?_⟩
    rw [map_div₀, eq_div_iff l']
    simpa [mul_comm] using h
  by_cases b0 : B = 0
  · subst B
    refine ⟨ratFunc_constant_of_pow (n := 2) (c := m/k) (by decide) ?_, ⟨0, by simp⟩⟩
    rw [map_div₀, eq_div_iff k']
    simpa [mul_comm] using h
  let a := A.num
  let b := B.num
  let P := A.denom
  let Q := B.denom
  have qa : IsCoprime a P := A.isCoprime_num_denom
  have qb : IsCoprime b Q := B.isCoprime_num_denom
  have ea : emb a = A * emb P := (div_eq_iff (RatFunc.algebraMap_ne_zero A.denom_ne_zero)).mp A.num_div_denom
  have eb : emb b = B * emb Q := (div_eq_iff (RatFunc.algebraMap_ne_zero B.denom_ne_zero)).mp B.num_div_denom
  have eq : C k*a^2*Q^3 + C l*b^3*P^2 = C m*P^2*Q^3 := by
    apply RatFunc.algebraMap_injective K
    change emb _ = emb _
    simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_C, ea, eb]
    linear_combination (emb P)^2 * (emb Q)^3 * h
  have dP : P^2 ∣ Q^3 := by
    have hc : IsCoprime (P^2) (C k*a^2) :=
      (isCoprime_mul_unit_left_right (hk.isUnit.map C) _ _).mpr qa.symm.pow_left.pow_right
    exact hc.dvd_of_dvd_mul_left ⟨C m*Q^3-C l*b^3, by linear_combination eq⟩
  have dQ : Q^3 ∣ P^2 := by
    have hc : IsCoprime (Q^3) (C l*b^3) :=
      (isCoprime_mul_unit_left_right (hl.isUnit.map C) _ _).mpr qb.symm.pow_left.pow_right
    exact hc.dvd_of_dvd_mul_left ⟨C m*P^2-C k*a^2, by linear_combination eq⟩
  have denEq : P^2 = Q^3 := eq_of_monic_of_associated
    (A.monic_denom.pow _) (B.monic_denom.pow _) (associated_of_dvd_dvd dP dQ)
  have qn : Q ≠ 0 := B.denom_ne_zero
  obtain ⟨s, hs⟩ : Q ∣ P := (IsIntegrallyClosed.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    (denEq ▸ pow_dvd_pow Q (by decide : 2 ≤ 3))
  have es : s^2 = Q := by
    apply mul_left_cancel₀ (pow_ne_zero 2 qn)
    rw [← mul_pow, ← hs, denEq, pow_succ]
  have ep : P = s^3 := by rw [hs, ← es]; ring
  have sn : s ≠ 0 := by rintro rfl; simp at es; exact qn es.symm
  have fc : C k*a^2 + C (-m)*s^6 + C l*b^3 = 0 := by
    have hpow : (s^2)^3 = s^6 := by ring
    have hpow' : (s^3)^2 = s^6 := by ring
    rw [ep, ← es, hpow, hpow'] at eq
    apply mul_right_cancel₀ (pow_ne_zero 6 sn)
    rw [zero_mul, map_neg]
    linear_combination eq
  have cop := qa.of_isCoprime_of_dvd_right (ep ▸ dvd_pow_self s (by decide : 3 ≠ 0))
  obtain ⟨da, ds, db⟩ := Polynomial.flt_catalan (p := 2) (q := 6) (r := 3)
    (by decide) (by decide) (by decide) (by decide) (by simpa using h₂)
    (by convert mul_ne_zero h₂ h₃ using 1; norm_num) (by simpa using h₃)
    (RatFunc.num_ne_zero a0) sn (RatFunc.num_ne_zero b0) cop hk (neg_ne_zero.mpr hm) hl fc
  constructor
  · apply (RatFunc.eq_C_iff A).mpr
    refine ⟨da, ?_⟩
    change P.natDegree = 0
    rw [ep, natDegree_pow, ds, mul_zero]
  · apply (RatFunc.eq_C_iff B).mpr
    refine ⟨db, ?_⟩
    change Q.natDegree = 0
    rw [← es, natDegree_pow, ds, mul_zero]

/-- The characteristic-zero specialization for rational polynomial searches. -/
theorem ratFunc_mordell_constants (k l m : ℚ) (hk : k ≠ 0) (hl : l ≠ 0) (hm : m ≠ 0)
    (A B : RatFunc ℚ) (h : RatFunc.C k*A^2 + RatFunc.C l*B^3 = RatFunc.C m) :
    (∃ a : ℚ, A = RatFunc.C a) ∧ (∃ b : ℚ, B = RatFunc.C b) :=
  ratFunc_mordell_constants_over (by decide) (by decide) k l m hk hl hm A B h

private theorem constant_x_of_constant_z {x y z : RatFunc ℚ} {c : ℚ}
    (he : z^2 + y^2*z + x^3 = 2) (hz : z = RatFunc.C c) :
    ∃ b : ℚ, x = RatFunc.C b := by
  subst z
  by_cases hc : c = 0
  · subst c
    apply ratFunc_constant_of_pow (n := 3) (c := 2) (by decide)
    simpa using he
  have hm : 2 - c^2 ≠ 0 := by
    intro h
    have sq : IsSquare ((2 : ℕ) : ℚ) := ⟨c, by change (2 : ℚ) = c*c; linear_combination h⟩
    exact Nat.prime_two.not_isSquare (Rat.isSquare_natCast_iff.mp sq)
  apply (ratFunc_mordell_constants c 1 (2 - c^2) hc one_ne_zero hm y x ?_).2
  simp only [map_one, one_mul, map_sub, map_ofNat, map_pow]
  linear_combination he

/-- On the cubic surface, a constant y, z, or z+y² forces x to be constant. -/
theorem constant_x_of_constant_fiber {x y z : RatFunc ℚ}
    (he : z^2+y^2*z+x^3=2)
    (h : (∃ c : ℚ, y = RatFunc.C c) ∨ (∃ c : ℚ, z = RatFunc.C c) ∨
      (∃ c : ℚ, z+y^2 = RatFunc.C c)) : ∃ b : ℚ, x = RatFunc.C b := by
  rcases h with ⟨c,rfl⟩ | ⟨c,hc⟩ | ⟨c,hc⟩
  · apply (ratFunc_mordell_constants 1 4 (c^4+8) one_ne_zero (by decide) (by positivity)
      (2*z+(RatFunc.C c)^2) x ?_).2
    simp only [map_one, one_mul, map_add, map_ofNat, map_pow]
    linear_combination 4*he
  · exact constant_x_of_constant_z he hc
  · apply constant_x_of_constant_z (z := -(z+y^2)) (y := y) (c := -c)
    · linear_combination he
    · rw [hc,map_neg]

end SmallCubic
