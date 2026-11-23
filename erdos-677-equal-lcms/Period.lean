import PrimePowers

namespace Erdos677

open Finset

private theorem gcd_next_hits {n k p e : ℕ} (hk : 0 < k) (hp : p.Prime) :
    p ^ e ∣ (lcmInterval n k).gcd (n + k + 1) ↔
      ∃ t, 0 < t ∧ t ≤ k ∧ p ^ e ∣ t ∧ p ^ e ∣ n + k + 1 := by
  rw [Nat.dvd_gcd_iff, primePower_dvd_interval hp hk]
  constructor
  · rintro ⟨⟨x, hx₁, hx₂, hx⟩, hlast⟩
    exact ⟨n + k + 1 - x, by omega, by omega, Nat.dvd_sub hlast hx, hlast⟩
  · rintro ⟨t, ht₁, ht₂, ht, hlast⟩
    exact ⟨⟨n + k + 1 - t, by omega, by omega, Nat.dvd_sub hlast ht⟩, hlast⟩

/-- The common factor removed when the next entry is appended repeats under any
shift divisible by all preceding offsets. -/
theorem gcd_next_periodic {n k d : ℕ} (hk : 0 < k)
    (hd : ∀ t, 0 < t → t ≤ k → t ∣ d) :
    (lcmInterval n k).gcd (n + k + 1) =
      (lcmInterval (n + d) k).gcd (n + d + k + 1) := by
  have hits (p e : ℕ) (hp : p.Prime) :
      p ^ e ∣ (lcmInterval n k).gcd (n + k + 1) ↔
      p ^ e ∣ (lcmInterval (n + d) k).gcd (n + d + k + 1) := by
    rw [gcd_next_hits hk hp, gcd_next_hits hk hp]
    have shift (t) (ht₁ : 0 < t) (ht₂ : t ≤ k) (ht : p ^ e ∣ t) :
        p ^ e ∣ n + k + 1 ↔ p ^ e ∣ n + d + k + 1 := by
      rw [show n + d + k + 1 = n + k + 1 + d by omega]
      exact Nat.dvd_add_iff_left (ht.trans (hd t ht₁ ht₂))
    constructor <;> rintro ⟨t, ht₁, ht₂, ht, h⟩
    · exact ⟨t, ht₁, ht₂, ht, (shift t ht₁ ht₂ ht).mp h⟩
    · exact ⟨t, ht₁, ht₂, ht, (shift t ht₁ ht₂ ht).mpr h⟩
  exact Nat.dvd_antisymm
    ((Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr fun p e hp => (hits p e hp).mp)
    ((Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr fun p e hp => (hits p e hp).mpr)

/-- For every positive block length, its interval LCM increases strictly under any
positive shift divisible by each of the smaller positive integers. -/
theorem strict_increase_of_common_multiple_shift (n : ℕ) {k d : ℕ} (hk : 0 < k)
    (hd : 0 < d) (hdiv : ∀ t, 0 < t → t < k → t ∣ d) :
    lcmInterval n k < lcmInterval (n + d) k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk' : k = 0
    · subst k
      simpa [lcmInterval, Nat.Ioc_succ_singleton] using
        (show n + 1 < n + d + 1 by omega)
    have hprev := ih (by omega) (fun t ht ht' => hdiv t ht (by omega))
    have hprod : lcmInterval n k * (n + k + 1) <
        lcmInterval (n + d) k * (n + d + k + 1) :=
      Nat.mul_lt_mul_of_lt_of_le hprev (by omega) (by omega)
    rw [← Nat.gcd_mul_lcm, ← Nat.gcd_mul_lcm (lcmInterval (n + d) k),
      ← gcd_next_periodic (n := n) (d := d) (by omega) (fun t ht ht' => hdiv t ht (by omega))]
      at hprod
    simpa only [lcmInterval_extend] using Nat.lt_of_mul_lt_mul_left hprod

/-- In particular, two blocks of length two have distinct LCMs at all distinct starts. -/
theorem length_two_strict (n : ℕ) {d : ℕ} (hd : 0 < d) :
    lcmInterval n 2 < lcmInterval (n + d) 2 := by
  apply strict_increase_of_common_multiple_shift n (by decide) hd
  intro t ht h₂
  have : t = 1 := by omega
  simp [this]

end Erdos677
