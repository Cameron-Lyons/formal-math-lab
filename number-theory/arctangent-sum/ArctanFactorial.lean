module

public import ArctanPrimeInterval
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

namespace Arxiv.«2607.05739»

/-- Primes giving a lower bound for the part of a factorial coprime to the norm. -/
def inertPrimes : Finset ℕ := (Nat.primesLE 32768).filter (fun p => p % 4 = 3)

def factorialWeight (n : ℕ) : ℕ := ∑ p ∈ inertPrimes, p.log2 * (n / p)

def inertFactor (n : ℕ) : ℕ := ∏ p ∈ inertPrimes, p ^ (n / p)

private theorem prime_of_mem {p : ℕ} (h : p ∈ inertPrimes) : p.Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_filter.mp h).1

theorem inertFactor_dvd_factorial (n : ℕ) : inertFactor n ∣ n.factorial := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp (((Nat.coprime_primes (prime_of_mem hp)
      (prime_of_mem hq)).mpr hpq).pow_left _ |>.pow_right _)
  · intro p hp
    have hprime := prime_of_mem hp
    apply dvd_trans _ (Nat.factorial_dvd_factorial (Nat.mul_div_le n p))
    rw [hprime.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _),
      Nat.factorization_factorial_mul hprime]
    omega

theorem inertFactor_coprime_norm (n : ℕ) : (inertFactor n).Coprime (normProduct n) := by
  apply Nat.Coprime.prod_left
  intro p hp
  let _ : Fact p.Prime := ⟨prime_of_mem hp⟩
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.prod_right
  intro k _
  apply (prime_of_mem hp).coprime_iff_not_dvd.mpr
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at hz
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one
    (show (k : ZMod p) ^ 2 = -1 by linear_combination hz) (Finset.mem_filter.mp hp).2

theorem two_pow_weight_le (n : ℕ) : 2 ^ factorialWeight n ≤ inertFactor n := by
  unfold factorialWeight inertFactor
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  intro p hp
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.log2_self_le (prime_of_mem hp).ne_zero) _

theorem weight_blocks (n b : ℕ) : (n / b) * factorialWeight b ≤ factorialWeight n := by
  unfold factorialWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [mul_left_comm]
  apply Nat.mul_le_mul_left
  apply (Nat.le_div_iff_mul_le (prime_of_mem hp).pos).mpr
  rw [Nat.mul_assoc]
  exact (Nat.mul_le_mul_left _ (Nat.div_mul_le_self b p)).trans (Nat.div_mul_le_self n b)

theorem factorial_weight_large {n : ℕ} (hn : 2 ^ 27 ≤ n)
    (hcert : 5700000 ≤ factorialWeight 1000000) : 11 * n < 2 * factorialWeight n := by
  have h := (Nat.mul_le_mul_left (n / 1000000) hcert).trans (weight_blocks n 1000000)
  omega

end Arxiv.«2607.05739»
