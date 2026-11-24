module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Changing the parameter and reducing the coefficient identity at a valuation.
Mathlib uses multiplicative valuations; an integral coefficient has value ≤ 1. -/
public section

open Polynomial
open scoped Polynomial

namespace SmallCubic

/-- For a finite collection of nonzero coefficients of positive index,
choose the greatest of the slopes −ord(aᵢ)/i. A negative input valuation
makes this slope positive and some resulting valuation is exactly zero. -/
theorem coefficient_balancing_slope {ι : Type*} (S : Finset ι)
    (index : ι → ℕ) (ord : ι → ℤ) (hi : ∀ j ∈ S, 0 < index j)
    (hneg : ∃ j ∈ S, ord j < 0) :
    ∃ s : ℚ, 0 < s ∧
      (∀ j ∈ S, 0 ≤ (ord j : ℚ) + (index j : ℚ)*s) ∧
      ∃ j ∈ S, (ord j : ℚ) + (index j : ℚ)*s = 0 := by
  obtain ⟨k, hk, hneg⟩ := hneg
  let slope (j : ι) : ℚ := -(ord j : ℚ)/(index j : ℚ)
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image slope ⟨k, hk⟩
  have ipos (i : ι) (h : i ∈ S) : (0 : ℚ) < index i := by exact_mod_cast hi i h
  refine ⟨slope j, ?_, ?_, j, hj, ?_⟩
  · apply lt_of_lt_of_le _ (hmax k hk)
    exact div_pos (neg_pos.mpr (by exact_mod_cast hneg)) (ipos k hk)
  · intro i h
    have hle := (div_le_iff₀ (ipos i h)).mp (hmax i h)
    linarith
  · dsimp [slope]
    field_simp [ne_of_gt (ipos j hj)]
    ring

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- The coefficients of p(l T) descend to the valuation ring as soon as their
magnitudes are bounded by one. -/
theorem lift_scaled_polynomial (v : Valuation K Γ) (l : K) (p : K[X])
    (h : ∀ n, v (p.coeff n) * v l ^ n ≤ 1) :
    ∃ P : v.valuationSubring[X], P.map v.valuationSubring.subtype = p.comp (C l * X) := by
  apply (mem_map_range v.valuationSubring.subtype).2
  intro n
  rw [comp_C_mul_X_coeff]
  refine ⟨⟨_, (v.mem_valuationSubring_iff _).mpr ?_⟩, rfl⟩
  change v (p.coeff n * l^n) ≤ 1
  simpa only [map_mul, map_pow] using h n

private theorem scaled_coeff {v : Valuation K Γ} {l : K} {p : K[X]}
    {P : v.valuationSubring[X]} (hP : P.map v.valuationSubring.subtype = p.comp (C l * X))
    (n : ℕ) : (P.coeff n : K) = p.coeff n * l ^ n := by
  have := congrArg (fun f : K[X] => f.coeff n) hP
  simpa [coeff_map] using this

/-- A coefficient attaining the slope bound survives reduction, so its term
gives a lower bound for the degree. -/
theorem scaled_residue_survives {v : Valuation K Γ} {l : K} {p : K[X]}
    {P : v.valuationSubring[X]} (hP : P.map v.valuationSubring.subtype = p.comp (C l * X))
    (n : ℕ) (hn : v (p.coeff n) * v l ^ n = 1) :
    n ≤ (P.map (IsLocalRing.residue _)).natDegree := by
  apply le_natDegree_of_ne_zero
  rw [coeff_map, ne_eq, IsLocalRing.residue_eq_zero_iff, v.mem_maximalIdeal_iff]
  rw [scaled_coeff hP n, map_mul, map_pow, hn]
  exact lt_irrefl _

private theorem scaled_residue_degree_le {v : Valuation K Γ} {l : K} {p : K[X]}
    {P : v.valuationSubring[X]} (hP : P.map v.valuationSubring.subtype = p.comp (C l * X)) :
    (P.map (IsLocalRing.residue _)).natDegree ≤ p.natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  have hc : (P.coeff n : K) = 0 := by
    rw [scaled_coeff hP n, coeff_eq_zero_of_natDegree_lt hn, zero_mul]
  have h0 : P.coeff n = 0 := Subtype.ext hc
  simp [coeff_map, h0]

/-- Shrinking the coordinate by a balancing element produces a nonconstant
ordinary polynomial solution in the residue field. The hypotheses specify
the balancing inequalities and one coefficient attaining equality at a
positive index. Each degree stays within the original numerator bound. -/
theorem specialize_pole_two_at_a_slope (v : Valuation K Γ) (l D : K)
    (hl : v l < 1) (hD : v D ≤ 1) (x y w : K[X])
    (hx : ∀ n, v (x.coeff n) * v l ^ n ≤ 1)
    (hy : ∀ n, v (y.coeff n) * v l ^ n ≤ 1)
    (hw : ∀ n, v (w.coeff n) * v l ^ n ≤ 1)
    (hit : ∃ n > 0, v (x.coeff n) * v l ^ n = 1 ∨
      v (y.coeff n) * v l ^ n = 1 ∨ v (w.coeff n) * v l ^ n = 1)
    (heq : w^2 + 4*x^3 = y^4*(1 - C D * X^2)^2 + 8*(1 - C D * X^2)^6) :
    ∃ X₀ Y₀ W₀ : (IsLocalRing.ResidueField v.valuationSubring)[X],
      W₀^2 + 4*X₀^3 = Y₀^4 + 8 ∧
      X₀.natDegree ≤ x.natDegree ∧ Y₀.natDegree ≤ y.natDegree ∧ W₀.natDegree ≤ w.natDegree ∧
      (0 < X₀.natDegree ∨ 0 < Y₀.natDegree ∨ 0 < W₀.natDegree) := by
  obtain ⟨A, hA⟩ := lift_scaled_polynomial v l x hx
  obtain ⟨B, hB⟩ := lift_scaled_polynomial v l y hy
  obtain ⟨E, hE⟩ := lift_scaled_polynomial v l w hw
  have hsmall : v (D*l^2) < 1 := by
    rw [map_mul, map_pow]
    calc v D * v l ^ 2 ≤ 1 * v l ^ 2 := mul_le_mul_left hD _
      _ < 1 := by simpa using pow_lt_one₀ zero_le hl (by decide : 2 ≠ 0)
  let d : v.valuationSubring := ⟨D*l^2, (v.mem_valuationSubring_iff _).mpr hsmall.le⟩
  have hd : IsLocalRing.residue v.valuationSubring d = 0 := by
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((v.mem_maximalIdeal_iff).mpr hsmall)
  have heqO : E^2+4*A^3 = B^4*(1-C d*X^2)^2 + 8*(1-C d*X^2)^6 := by
    apply Polynomial.map_injective v.valuationSubring.subtype Subtype.val_injective
    have hscaled := congrArg (fun P : K[X] => P.comp (C l * X)) heq
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      d, hA, hB, hE, add_comp, mul_comp, pow_comp, sub_comp] at hscaled ⊢
    convert hscaled using 1
    ring
  let res := IsLocalRing.residue v.valuationSubring
  refine ⟨A.map res, B.map res, E.map res, ?_, scaled_residue_degree_le hA,
    scaled_residue_degree_le hB, scaled_residue_degree_le hE, ?_⟩
  · simpa [res, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_sub, hd] using congrArg (Polynomial.map res) heqO
  · obtain ⟨n, hn, h | h | h⟩ := hit
    · exact Or.inl (hn.trans_le (scaled_residue_survives hA n h))
    · exact Or.inr (Or.inl (hn.trans_le (scaled_residue_survives hB n h)))
    · exact Or.inr (Or.inr (hn.trans_le (scaled_residue_survives hE n h)))

/-- When all negative Laurent coefficients have value < 1, reduction
removes the denominator X^m. A coefficient of value one at exponent j
certifies that the resulting polynomial has degree at least j. -/
theorem remove_reduced_laurent_denominator (v : Valuation K Γ)
    (P : v.valuationSubring[X]) (m : ℕ)
    (h : ∀ i < m, v (P.coeff i : K) < 1) :
    ∃ p : (IsLocalRing.ResidueField v.valuationSubring)[X],
      P.map (IsLocalRing.residue _) = X^m*p ∧ p.natDegree ≤ P.natDegree - m ∧
      ∀ j, v (P.coeff (j+m) : K) = 1 → j ≤ p.natDegree := by
  have hdvd : X^m ∣ P.map (IsLocalRing.residue _) := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    rw [coeff_map, IsLocalRing.residue_eq_zero_iff, v.mem_maximalIdeal_iff]
    exact h i hi
  obtain ⟨p, hp⟩ := hdvd
  refine ⟨p, hp, ?_, ?_⟩
  · by_cases h0 : p = 0
    · simp [h0]
    · have hle : (P.map (IsLocalRing.residue _)).natDegree ≤ P.natDegree := natDegree_map_le
      rw [hp, natDegree_X_pow_mul m h0] at hle
      omega
  · intro j hj
    apply le_natDegree_of_ne_zero
    rw [← coeff_X_pow_mul p m j, ← hp, coeff_map, ne_eq, IsLocalRing.residue_eq_zero_iff,
      v.mem_maximalIdeal_iff, hj]
    exact lt_irrefl _

/-- For the rescaling toward a Laurent pole, start with the three scaled
integral numerators of x,y,w after clearing their denominators X²,X,X³.
The coefficients at negative exponents vanish in the residue field while
the selected positive exponent survives. -/
theorem specialize_pole_two_towards_infinity (v : Valuation K Γ)
    (A B E : v.valuationSubring[X])
    (hA : ∀ i < 2, v (A.coeff i : K) < 1)
    (hB : ∀ i < 1, v (B.coeff i : K) < 1)
    (hE : ∀ i < 3, v (E.coeff i : K) < 1)
    (hit : ∃ j > 0, v (A.coeff (j+2) : K) = 1 ∨
      v (B.coeff (j+1) : K) = 1 ∨ v (E.coeff (j+3) : K) = 1)
    (heq : E^2 + 4*A^3 = X^2*B^4 + 8*X^6) :
    ∃ x y w : (IsLocalRing.ResidueField v.valuationSubring)[X],
      w^2 + 4*x^3 = y^4 + 8 ∧
      x.natDegree ≤ A.natDegree - 2 ∧ y.natDegree ≤ B.natDegree - 1 ∧
      w.natDegree ≤ E.natDegree - 3 ∧ (0 < x.natDegree ∨ 0 < y.natDegree ∨ 0 < w.natDegree) := by
  obtain ⟨x, hx, dx, sx⟩ := remove_reduced_laurent_denominator v A 2 hA
  obtain ⟨y, hy, dy, sy⟩ := remove_reduced_laurent_denominator v B 1 hB
  obtain ⟨w, hw, dw, sw⟩ := remove_reduced_laurent_denominator v E 3 hE
  refine ⟨x, y, w, ?_, dx, dy, dw, ?_⟩
  · have eq := congrArg (Polynomial.map (IsLocalRing.residue _)) heq
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_ofNat, map_X, hx, hy, hw] at eq
    apply mul_left_cancel₀ (pow_ne_zero 6 (X_ne_zero (R := IsLocalRing.ResidueField v.valuationSubring)))
    linear_combination eq
  · obtain ⟨j, hj, h | h | h⟩ := hit
    · exact Or.inl (hj.trans_le (sx j h))
    · exact Or.inr (Or.inl (hj.trans_le (sy j h)))
    · exact Or.inr (Or.inr (hj.trans_le (sw j h)))

end SmallCubic
