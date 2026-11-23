import UpstreamInterval
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos677

open Finset

private theorem primePower_dvd_lcm {p e a b : ℕ} (hp : p.Prime) :
    p ^ e ∣ a.lcm b ↔ p ^ e ∣ a ∨ p ^ e ∣ b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha hb),
    hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb,
    Nat.factorization_lcm ha hb, Finsupp.sup_apply, le_max_iff]

private theorem primePower_dvd_finset {p e : ℕ} (hp : p.Prime) {s : Finset ℕ}
    (hs : s.Nonempty) : p ^ e ∣ s.lcm id ↔ ∃ x ∈ s, p ^ e ∣ x := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha _ ih =>
    simp [Finset.cons_eq_insert, Finset.lcm_insert, lcm_eq_nat_lcm,
      primePower_dvd_lcm hp, ih]

/-- A prime power divides the interval LCM precisely when one entry is a multiple. -/
theorem primePower_dvd_interval {n k p e : ℕ} (hp : p.Prime) (hk : 0 < k) :
    p ^ e ∣ lcmInterval n k ↔ ∃ x, n < x ∧ x ≤ n + k ∧ p ^ e ∣ x := by
  have hs : (Ioc n (n + k)).Nonempty := ⟨n + k, mem_Ioc.mpr ⟨by omega, le_rfl⟩⟩
  simpa [lcmInterval, and_assoc] using primePower_dvd_finset (e := e) hp hs

/-- A comparison between two integer quotients detects a multiple in an interval. -/
theorem contains_multiple_iff {n k q : ℕ} (hq : 0 < q) :
    (∃ x, n < x ∧ x ≤ n + k ∧ q ∣ x) ↔ n / q < (n + k) / q := by
  constructor
  · rintro ⟨x, hx, hx', hqx⟩
    apply lt_of_lt_of_le _ (Nat.div_le_div_right hx')
    exact (Nat.div_lt_iff_lt_mul hq).mpr (by rwa [Nat.div_mul_cancel hqx])
  · intro h
    exact ⟨(n + k) / q * q, (Nat.div_lt_iff_lt_mul hq).mp h,
      Nat.div_mul_le_self _ _, dvd_mul_left ..⟩

/-- The exact prime-power filter for blocks of a common positive length. -/
theorem equal_iff_primePower_hits {m n k : ℕ} (hk : 0 < k) :
    lcmInterval m k = lcmInterval n k ↔ ∀ p e : ℕ, p.Prime →
      (m / p ^ e < (m + k) / p ^ e ↔ n / p ^ e < (n + k) / p ^ e) := by
  have hit (a p e : ℕ) (hp : p.Prime) :
      p ^ e ∣ lcmInterval a k ↔ a / p ^ e < (a + k) / p ^ e :=
    (primePower_dvd_interval hp hk).trans (contains_multiple_iff (pow_pos hp.pos e))
  constructor
  · intro h p e hp
    rw [← hit m p e hp, ← hit n p e hp, h]
  · intro h
    apply Nat.dvd_antisymm
    · apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
      exact fun p e hp hd => (hit n p e hp).mpr ((h p e hp).mp ((hit m p e hp).mp hd))
    · apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
      exact fun p e hp hd => (hit m p e hp).mpr ((h p e hp).mpr ((hit n p e hp).mp hd))

/-- Appending one integer to a block takes the LCM with that integer. -/
theorem lcmInterval_extend (n k : ℕ) :
    lcmInterval n (k + 1) = (lcmInterval n k).lcm (n + k + 1) := by
  have hset : Ioc n (n + (k + 1)) = insert (n + k + 1) (Ioc n (n + k)) := by
    ext x
    simp only [mem_insert, mem_Ioc]
    omega
  simp only [lcmInterval, hset, Finset.lcm_insert, lcm_eq_nat_lcm, id_eq]
  exact Nat.lcm_comm ..

end Erdos677
