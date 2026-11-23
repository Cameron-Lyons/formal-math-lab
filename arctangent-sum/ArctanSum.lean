module

public import ArctanFinite
public import ArctanModular
public import ArctanSparsity
public import ArctanValueBound

/-!
# Partial results on the arctangent-sum conjecture

The conjecture says that among positive indices, xₙ is an integer exactly
when n = 1, 2, 3 or 4. The following partial results are proved here.

* `counterexample_constraints` uses the Gaussian coordinates xₙ = Bₙ/Aₙ.
  A certified interval check excludes indices 5 through 10⁶. If Bₙ = m Aₙ,
  the squared norm equals Aₙ²(1+m²). Its prime factors give |m| > n¹⁰.
* `positive_integer_count_isBigO` counts the integer values through N.
  Each gives a distinct label of size O(log N). The determinant and
  pair count in `ArctanSparsity` give O((log N)^(3/4)) such labels.

* [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean)
* [Ono's sparsity theorem](https://arxiv.org/abs/2607.05739)
* [Moll's arithmetic progressions](https://www.math.tulane.edu/~vhm/papers_html/xn-final.pdf)
* [Cilleruelo's norm-product argument](https://matematicas.uam.es/~franciscojavier.cilleruelo/Papers/squares-sinlogo.pdf)
-/

public section

namespace Arxiv.«2607.05739»

/-- Every counterexample would have index above one million and magnitude greater than n¹⁰. -/
theorem counterexample_constraints {n : ℕ} {m : ℤ} (hn : 5 ≤ n)
    (h : Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) = (m : ℝ)) :
    1000000 < n ∧ n^10 < m.natAbs ∧ 10^60 < m.natAbs := by
  have hn' : 1000000 < n := by
    by_contra! hsmall
    exact not_isIntegerValue_five_to_one_million hn hsmall ((isIntegerValue_iff_tan n).mpr ⟨m, h⟩)
  have hm := index_pow_ten_lt_natAbs hn (tan_eq_int_iff.mp h)
  refine ⟨hn', hm, lt_trans ?_ hm⟩
  change (1000000 : ℕ)^10 < n^10
  exact Nat.pow_lt_pow_left hn' (by decide)

open Filter Asymptotics
open scoped Classical

/-- The number of positive indices n ≤ N with integer tangent is O((log N)^(3/4)). -/
theorem positive_integer_count_isBigO :
    (fun N : ℕ => (((Finset.Icc 1 N).filter IsIntegerValue).card : ℝ)) =O[atTop]
      (fun N : ℕ => (Real.log N)^(3/4 : ℝ)) := by
  let early := (Finset.Ico 1 5).filter IsIntegerValue
  apply (event_count_add_isBigO_log_three_quarters early.card integer_event_count_fourth).congr'
    _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (5 : ℕ)] with N hN
  rw [← integerCount_eq_prefix, ← Nat.cast_add, Nat.cast_inj, add_comm]
  have hsplit := Finset.Ico_union_Ico_eq_Ico (by decide : 1 ≤ 5) (by omega : 5 ≤ N+1)
  have hdisj := Finset.Ico_disjoint_Ico_consecutive 1 5 (N+1)
  rw [← Finset.Ico_add_one_right_eq_Icc 1 N, ← hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
  rw [Finset.Ico_add_one_right_eq_Icc 5 N]
  rfl

/-- The four values actually attained in the verified value window. -/
theorem known_values :
    B 1 = A 1 * 1 ∧ B 2 = A 2 * (-3) ∧ B 3 = A 3 * 0 ∧ B 4 = A 4 * 4 := by
  decide

theorem tan_ne_int_through_ten_thousand {n : ℕ} (hn : 5 ≤ n) (hn' : n ≤ 10000) (m : ℤ) :
    Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) ≠ (m : ℝ) :=
  fun h => not_isIntegerValue_five_to_ten_thousand hn hn' ((isIntegerValue_iff_tan n).mpr ⟨m, h⟩)

theorem tan_int_of_abs_le_million {n : ℕ} {m : ℤ} (hm : |m| ≤ 1000000)
    (h : Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) = (m : ℝ)) :
    m = -3 ∨ m = 0 ∨ m = 1 ∨ m = 4 :=
  integer_value_of_abs_le_million hm (tan_eq_int_iff.mp h)

/-- A large simple prime factor exists at every index beyond the square norm at index three. -/
theorem exists_large_prime {n : ℕ} (hn : 4 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ 2*n < p ∧ p ∣ normProduct n := by
  by_cases h : n < 2^27
  · exact exists_large_prime_small hn (by omega)
  · exact large_prime_of_estimates (by omega) factorialWeight_certificate

/-- Any counterexample to the arctangent-sum conjecture has magnitude above one million. -/
theorem tan_int_large {n : ℕ} {m : ℤ} (hn : 5 ≤ n)
    (h : Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) = (m : ℝ)) :
    1000000 < |m| :=
  million_lt_abs_of_five_le hn (tan_eq_int_iff.mp h)

/-- Precisely the first four positive indices give an integer in the stated range. -/
theorem bounded_integer_iff {n : ℕ} (hn : 0 < n) :
    (∃ m : ℤ, |m| ≤ 1000000 ∧
      Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) = (m : ℝ)) ↔ n ≤ 4 := by
  constructor
  · rintro ⟨m, hm, h⟩
    by_contra! hlarge
    exact (tan_int_large hlarge h).not_ge hm
  · intro h
    rcases known_values with ⟨h₁, h₂, h₃, h₄⟩
    rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 by omega) with rfl | rfl | rfl | rfl
    · exact ⟨1, by decide, tan_eq_int_iff.mpr h₁⟩
    · exact ⟨-3, by decide, tan_eq_int_iff.mpr h₂⟩
    · exact ⟨0, by decide, tan_eq_int_iff.mpr h₃⟩
    · exact ⟨4, by decide, tan_eq_int_iff.mpr h₄⟩

/-- An effective exponential lower bound on the size of a large-index integer value. -/
theorem tan_int_exponential {n : ℕ} {m : ℤ} (hn : 2^27 ≤ n)
    (h : Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) = (m : ℝ)) :
    2^(n / 4) ≤ 1 + m.natAbs^2 :=
  exp_bound_of_estimates hn factorialWeight_certificate (tan_eq_int_iff.mp h)

/-- Every index in a certified residue class is excluded, with no upper bound on n. -/
theorem not_isIntegerValue_of_residue {p n : ℕ} (hp : p.Prime) (hmod : p % 4 = 3)
    (hr : ((coords (n % p)).1 : ZMod p) = 0) : ¬ IsIntegerValue n := by
  let _ : Fact p.Prime := ⟨hp⟩
  simpa only [Nat.div_add_mod] using not_isIntegerValue_of_inert_prime hmod hr (n / p)

theorem not_isIntegerValue_mod19 {n : ℕ} (h : n % 19 = 5 ∨ n % 19 = 13) :
    ¬ IsIntegerValue n := by
  apply not_isIntegerValue_of_residue (p := 19) (by decide) (by decide)
  rcases h with h | h <;> rw [h] <;> decide +kernel

set_option maxRecDepth 4096 in
theorem not_isIntegerValue_mod331 {n : ℕ}
    (h : n % 331 = 7 ∨ n % 331 = 77 ∨ n % 331 = 253 ∨ n % 331 = 323) :
    ¬ IsIntegerValue n := by
  apply not_isIntegerValue_of_residue (p := 331) (by decide) (by decide)
  rcases h with h | h | h | h <;> rw [h] <;> decide +kernel

end Arxiv.«2607.05739»
