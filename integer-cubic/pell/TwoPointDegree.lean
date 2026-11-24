module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

public section

namespace SmallCubic.TwoPoint

open Polynomial
open scoped Polynomial

/-- Multiplicities at any finite set of residue classes use at most the degree. -/
theorem sum_multiplicities_le {K : Type*} [Field K] (P : K[X]) (s : Finset K) :
    ∑ a ∈ s, P.rootMultiplicity a ≤ P.natDegree := by
  classical
  let t := s ∪ P.roots.toFinset
  calc
    ∑ a ∈ s, P.rootMultiplicity a = ∑ a ∈ s, P.roots.count a := by simp [count_roots]
    _ ≤ ∑ a ∈ t, P.roots.count a := Finset.sum_le_sum_of_subset (Finset.subset_union_left)
    _ = P.roots.card := Multiset.sum_count_eq_card (fun x hx => Finset.mem_union_right _ (by simpa using hx))
    _ ≤ P.natDegree := P.card_roots'

theorem two_orders_le {K : Type*} [Field K] (P : K[X]) {a b : K} (hab : a ≠ b)
    {r s : ℕ} (ha : r ≤ P.rootMultiplicity a) (hb : s ≤ P.rootMultiplicity b) :
    r+s ≤ P.natDegree := by
  classical
  have h := sum_multiplicities_le P ({a,b} : Finset K)
  simp [hab] at h
  omega

theorem no_two_fifth_order_roots {K : Type*} [Field K] (P : K[X]) {a b : K} (hab : a ≠ b)
    (hdeg : P.natDegree ≤ 8) (ha : 5 ≤ P.rootMultiplicity a) (hb : 5 ≤ P.rootMultiplicity b) :
    False := by
  have h := two_orders_le P hab ha hb
  omega

/-- Vanishing of the first k Taylor coefficients at a mark is exactly divisibility
by the kth power of its linear factor, also in positive characteristic. -/
theorem mark_pow_dvd_iff {K : Type*} [Field K] (P : K[X]) (a : K) (k : ℕ) :
    (X-C a)^k ∣ P ↔ ∀ i < k, (taylor a P).coeff i = 0 := by
  rw [← X_pow_dvd_iff]
  constructor
  · rintro ⟨Q,hQ⟩
    exact ⟨taylor a Q, by rw [hQ, taylor_mul, taylor_pow, taylor_X_sub_C]⟩
  · rintro ⟨Q,hQ⟩
    have h := congrArg (taylor (-a)) hQ
    refine ⟨taylor (-a) Q, ?_⟩
    simpa [taylor_taylor, taylor_mul, taylor_X_pow, sub_eq_add_neg] using h

/-- The vanishing criterion in the form used by a primitive residue polynomial. -/
theorem eq_zero_of_two_taylor_orders {K : Type*} [Field K] (P : K[X]) {a b : K} (hab : a ≠ b)
    (r s : ℕ) (hdeg : P.natDegree < r+s)
    (ha : ∀ i < r, (taylor a P).coeff i = 0) (hb : ∀ i < s, (taylor b P).coeff i = 0) :
    P = 0 := by
  by_contra hp
  have hr := (le_rootMultiplicity_iff hp).mpr ((mark_pow_dvd_iff P a r).mpr ha)
  have hs := (le_rootMultiplicity_iff hp).mpr ((mark_pow_dvd_iff P b s).mpr hb)
  exact (not_le_of_gt hdeg) (two_orders_le P hab hr hs)

/-- If the rescaled coefficient of index k has minimal valuation and the
rescaling slope is positive, every nonzero lower coefficient has unscaled
valuation strictly above the unscaled minimum. The common shift is arbitrary. -/
theorem valuation_gt_min_of_positive_slope (w : ℕ → ℚ) {i k : ℕ} (hik : i < k)
    {slope shift minimum : ℚ} (hs : 0 < slope) (hm : minimum ≤ w k)
    (hk : w k + (k : ℚ)*slope = shift) (hi : shift ≤ w i + (i : ℚ)*slope) :
    minimum < w i := by
  have h : (i : ℚ)*slope < (k : ℚ)*slope :=
    mul_lt_mul_of_pos_right (by exact_mod_cast hik) hs
  linarith

/-- A unit of index k at a positive slope forces the primitive reduction
to vanish to order k at the mark. Only coefficients that survive primitive
reduction need a finite additive valuation. -/
theorem mark_order_of_rescaling {K : Type*} [Field K] (P : K[X]) (a : K) (k : ℕ)
    (w : ℕ → ℚ) {slope shift minimum : ℚ} (hs : 0 < slope)
    (hk : w k + (k : ℚ)*slope = shift) (hm : minimum ≤ w k)
    (hsurv : ∀ i < k, (taylor a P).coeff i ≠ 0 →
      w i = minimum ∧ shift ≤ w i + (i : ℚ)*slope) :
    (X-C a)^k ∣ P := by
  apply (mark_pow_dvd_iff P a k).mpr
  intro i hi
  by_contra hn
  obtain ⟨hw,hscaled⟩ := hsurv i hi hn
  exact (ne_of_lt (valuation_gt_min_of_positive_slope w hi hs hm hk hscaled)) hw.symm

end SmallCubic.TwoPoint
