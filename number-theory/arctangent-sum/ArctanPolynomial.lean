module

public import ArctanExponential
public import ArctanPrimeMass
public import ArctanApprox
import Mathlib.Data.Nat.Prime.Factorial

public section

namespace Arxiv.«2607.05739»

private def primeProduct (s : Finset ℕ) := ∏ k ∈ s, (k^2 + 1)

/-- A single gcd certifies all the primes in a batch: each factor k²+1, if
composite, has a divisor between 2 and k. -/
private theorem batch_bound {s : Finset ℕ} {lo hi n : ℕ} {m : ℤ}
    (hc : (primeProduct s).Coprime lo.factorial)
    (hk : ∀ k ∈ s, 0 < k ∧ k ≤ lo ∧ hi+k < k^2+1)
    (hsize : hi^20 + 1 < primeProduct s) (hl : lo ≤ n) (hh : n ≤ hi)
    (h : B n = A n * m) : n^10 < m.natAbs := by
  have hprime (k : ℕ) (hks : k ∈ s) : (k^2+1).Prime := by
    obtain ⟨hk0, hklo, _⟩ := hk k hks
    -- A composite k²+1 would have a prime factor at most k ≤ lo.
    by_contra hcomp
    have hsmall := Nat.minFac_sq_le_self (by positivity : 0 < k^2+1) hcomp
    have hlarge : lo < (k^2+1).minFac := (Nat.coprime_factorial_iff (by nlinarith)).mp
      (hc.of_dvd_left (Finset.dvd_prod_of_mem (fun j : ℕ => j^2+1) hks))
    have := Nat.pow_le_pow_left (by omega : k+1 ≤ (k^2+1).minFac) 2
    nlinarith
  have hdiv : primeProduct s ∣ 1 + m.natAbs^2 := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro k hks j hjs hkj
      apply Nat.coprime_iff_isRelPrime.mp
      apply ((Nat.coprime_primes (hprime k hks) (hprime j hjs)).mpr)
      intro he
      apply hkj
      nlinarith
    · intro k hks
      obtain ⟨_, hklo, hkp⟩ := hk k hks
      obtain ⟨hd, hs⟩ := prime_once_on_interval (hprime k hks) rfl (hklo.trans hl) (by omega)
      have hpd := prime_dvd_one_add_sq_of_integerValue (hprime k hks) hd hs h
      exact_mod_cast (show ((k^2+1 : ℕ) : ℤ) ∣ ((1+m.natAbs^2 : ℕ) : ℤ) by simpa using hpd)
  have hbound := (Nat.le_of_dvd (by positivity : 0 < 1+m.natAbs^2) hdiv)
  by_contra! hsmall
  have hsq := (Nat.pow_le_pow_left hsmall 2).trans (Nat.pow_le_pow_left (Nat.pow_le_pow_left hh 10) 2)
  rw [← pow_mul, show (10 : ℕ) * 2 = 20 by decide] at hsq
  omega

private def primeWitnesses : Finset ℕ :=
  {50000, 49000, 48640, 48600, 48544, 48400, 48256, 48000, 47500,
   47396, 47096, 46546, 46400, 46250, 45254, 44800, 44206, 43904}

private theorem exp_dominates {n : ℕ} (hn : 2^27 ≤ n) : n^20+1 < 2^(n/4) := by
  have hcost (k : ℕ) (hk : 27 ≤ k) : 4*(20*(k+1)+1) ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k _ ih => rw [pow_succ]; omega
  have hn0 : n ≠ 0 := by omega
  have h := (hcost n.log2 ((Nat.le_log2 hn0).mpr hn)).trans (Nat.log2_self_le hn0)
  have hlt := Nat.pow_lt_pow_left (Nat.lt_log2_self (n := n)) (by decide : 20 ≠ 0)
  rw [← pow_mul] at hlt
  exact (Nat.succ_le_of_lt hlt).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : (n.log2+1)*20 < n/4))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- An integer value at any conjectured index would exceed the tenth power
of the index in absolute value. -/
theorem index_pow_ten_lt_natAbs {n : ℕ} {m : ℤ} (hn : 5 ≤ n)
    (h : B n = A n * m) : n^10 < m.natAbs := by
  by_cases h₀ : n ≤ 1000000
  · exact (not_isIntegerValue_five_to_one_million hn h₀ ⟨m, h⟩).elim
  by_cases h₂ : n ≤ 2^27
  · exact batch_bound (s := primeWitnesses) (lo := 50000) (hi := 2^27)
      (by rw [Nat.factorial_eq_factorialBinarySplitting]; decide +kernel)
      (by decide +kernel) (by decide +kernel) (by omega) h₂ h
  have hlarge : 2^27 ≤ n := by omega
  have he := (exp_dominates hlarge).trans_le (exp_bound_of_estimates hlarge factorialWeight_certificate h)
  by_contra! hsmall
  have hsq := Nat.pow_le_pow_left hsmall 2
  rw [← pow_mul, show (10 : ℕ) * 2 = 20 by decide] at hsq
  omega

end Arxiv.«2607.05739»
