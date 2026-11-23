module

public import A026019.Sequence
public import A026019.BinomialStep
public import A026019.RecurrenceAlgebra

/-!
# A026019: the conjectured three-term recurrence

The recurrence listed at <https://oeis.org/A026019> holds for every `n ≥ 2`.
The sequence is integer-valued, with binomial coefficients of negative lower
index interpreted as zero; `a_eq` states this convention explicitly.
-/

public section

namespace A026019

/-- The three-term recurrence, indexed without natural-number subtraction. -/
theorem recurrence_shifted (n : ℕ) :
    -2 * (2 * ((n : ℤ) + 2) + 3) * (13 * ((n : ℤ) + 2) - 9) *
        ((n : ℤ) + 2 + 1) * a (n + 2) +
      (499 * ((n : ℤ) + 2)^3 - 7 * ((n : ℤ) + 2)^2 -
        120 * ((n : ℤ) + 2) - 54) * a (n + 1) -
      3 * (3 * ((n : ℤ) + 2) - 5) * (37 * ((n : ℤ) + 2) - 24) *
        (3 * ((n : ℤ) + 2) - 4) * a n = 0 := by
  have h := recurrence_algebra (n : ℚ)
    (Nat.choose (3 * n) n : ℚ)
    (Nat.choose (3 * (n + 1)) (n + 1) : ℚ)
    (Nat.choose (3 * (n + 2)) (n + 2) : ℚ)
    (a n : ℚ) (a (n + 1) : ℚ) (a (n + 2) : ℚ)
    (by positivity) (closed_form_mul n)
    (by simpa only [Nat.cast_add, Nat.cast_one] using closed_form_mul (n + 1))
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using closed_form_mul (n + 2))
    (central_step n)
    (by simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one]
      using central_step (n + 1))
  exact_mod_cast h

/-- The exact OEIS recurrence, valid at every natural index `n ≥ 2`. -/
theorem recurrence (n : ℕ) (hn : 2 ≤ n) :
    -2 * (2 * (n : ℤ) + 3) * (13 * (n : ℤ) - 9) * ((n : ℤ) + 1) * a n +
      (499 * (n : ℤ)^3 - 7 * (n : ℤ)^2 - 120 * (n : ℤ) - 54) * a (n - 1) -
      3 * (3 * (n : ℤ) - 5) * (37 * (n : ℤ) - 24) * (3 * (n : ℤ) - 4) *
        a (n - 2) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.add_sub_cancel,
    show ∀ k : ℕ, k + 2 - 1 = k + 1 by omega] using recurrence_shifted k

end A026019
