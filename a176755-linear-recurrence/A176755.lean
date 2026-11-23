module

public import A176755.Sequence
public import A176755.GeneratingFunction
public import A176755.Differential
public import A176755.Coefficients

/-!
# Mathar's five-term recurrence for OEIS A176755

The nonlinear convolution recurrence implies a quadratic equation for the formal
generating function. Differentiation and polynomial elimination give a first-order
linear differential equation. Coefficient extraction gives the conjecture.
-/

public section

namespace A176755

/-- Mathar's conjectured five-term recurrence, in the indexing used by OEIS. -/
theorem mathar_of_recurrence (b : ℕ → ℤ)
    (h0 : b 0 = 1) (h1 : b 1 = 3)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      b (n + 1) = (∑ p ∈ Finset.range (n + 1), b p * b (n - p)) - 2)
    (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℤ) + 1) * b n +
      2 * (1 - 3 * (n : ℤ)) * b (n - 1) +
      ((n : ℤ) + 3) * b (n - 2) +
      2 * (10 * (n : ℤ) - 33) * b (n - 3) +
      16 * (4 - (n : ℤ)) * b (n - 4) = 0 := by
  have hq := quadratic_of_recurrence b h0 h1 hrec
  have hd := differential_of_quadratic (generatingFunction b) hq
  simpa using coefficients_of_differential (generatingFunction b) hd n hn

/-- The conjecture holds for the explicitly defined integer sequence A176755. -/
theorem mathar (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℤ) + 1) * a n +
      2 * (1 - 3 * (n : ℤ)) * a (n - 1) +
      ((n : ℤ) + 3) * a (n - 2) +
      2 * (10 * (n : ℤ) - 33) * a (n - 3) +
      16 * (4 - (n : ℤ)) * a (n - 4) = 0 :=
  mathar_of_recurrence a a_zero a_one a_recurrence n hn

end A176755
