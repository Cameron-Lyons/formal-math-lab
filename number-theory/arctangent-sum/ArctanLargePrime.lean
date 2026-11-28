module

public import ArctanValuation
public import ArctanPrimeCover
public import ArctanFactorial
public import ArctanOverhead

@[expose] public section

namespace Arxiv.«2607.05739»

def primePowerOverhead (n : ℕ) := ∏ p ∈ (2*n).primesLE, p ^ (Nat.log p (n^2+1) + Nat.log p (2*n))

private theorem overhead_pos (n : ℕ) : 0 < primePowerOverhead n :=
  Finset.prod_pos fun _ hp => pow_pos (Nat.prime_of_mem_primesLE hp).pos _

private theorem factorial_sq_le_norm (n : ℕ) : n.factorial ^ 2 ≤ normProduct n := by
  induction n with
  | zero => simp [normProduct]
  | succ n ih =>
    rw [Nat.factorial_succ, mul_pow, mul_comm]
    rw [show normProduct (n + 1) = normProduct n * (1 + (n + 1) ^ 2) from
      Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)) _]
    exact Nat.mul_le_mul ih (by omega)

/-- The norm divides the squared factorial times the valuation overhead, once
the factor R accounts for all prime divisors greater than 2n. -/
private theorem norm_dvd_with_large_primes {n R : ℕ} (hn : 0 < n) (hR : 0 < R)
    (hlarge : ∀ p : ℕ, p.Prime → 2*n < p → p ∣ normProduct n → p ∣ R) :
    normProduct n ∣ n.factorial ^ 2 * (primePowerOverhead n * R) := by
  have hpos := lt_of_lt_of_le (pow_pos (Nat.factorial_pos n) 2) (factorial_sq_le_norm n)
  apply (Nat.factorization_le_iff_dvd hpos.ne' (by positivity [overhead_pos n])).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hd : p ∣ normProduct n
    · rw [Nat.factorization_mul (by positivity) (Nat.mul_pos (overhead_pos n) hR).ne',
        Nat.factorization_mul (overhead_pos n).ne' hR.ne', Finsupp.add_apply, Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      by_cases hsmall : p ≤ 2*n
      · have hmem := Nat.mem_primesLE.mpr ⟨hsmall, hp⟩
        have hh : Nat.log p (n^2+1) + Nat.log p (2*n) ≤ (primePowerOverhead n).factorization p :=
          (hp.pow_dvd_iff_le_factorization (overhead_pos n).ne').mp
            (Finset.dvd_prod_of_mem (fun q => q ^ (Nat.log q (n^2+1) + Nat.log q (2*n))) hmem)
        have := normProduct_factorization_le hp hn
        omega
      · have hgt : 2*n < p := by omega
        have hshort := not_sq_dvd_normProduct_of_large_prime hp hgt hd
        rw [hp.pow_dvd_iff_le_factorization hpos.ne'] at hshort
        have hdiv : p ^ 1 ∣ R := by simpa using hlarge p hp hgt hd
        have := (hp.pow_dvd_iff_le_factorization hR.ne').mp hdiv
        omega
    · simp [Nat.factorization_eq_zero_of_not_dvd hd]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The inert factor of the factorial is coprime to the norm, so its square
must fit inside the valuation overhead and the large-prime contribution R. -/
theorem inertFactor_sq_le_overhead_mul {n R : ℕ} (hn : 0 < n) (hR : 0 < R)
    (hlarge : ∀ p : ℕ, p.Prime → 2*n < p → p ∣ normProduct n → p ∣ R) :
    (inertFactor n)^2 ≤ primePowerOverhead n * R := by
  have hd := norm_dvd_with_large_primes hn hR hlarge
  have hf := dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (inertFactor_dvd_factorial n) 2)
    (primePowerOverhead n * R)
  have hboth := ((inertFactor_coprime_norm n).pow_left 2).mul_dvd_of_dvd_of_dvd hf hd
  have hle := Nat.le_of_dvd (Nat.mul_pos (pow_pos (Nat.factorial_pos n) 2)
    (Nat.mul_pos (overhead_pos n) hR)) hboth
  have hfac := Nat.mul_le_mul_left ((inertFactor n)^2) (factorial_sq_le_norm n)
  apply Nat.le_of_mul_le_mul_right (c := n.factorial^2)
  · exact (hfac.trans hle).trans_eq (Nat.mul_comm _ _)
  · exact pow_pos (Nat.factorial_pos n) _

theorem weight_pow_le_mul_large_primes {n R : ℕ} (hn : 2^27 ≤ n) (hR : 0 < R)
    (hlarge : ∀ p : ℕ, p.Prime → 2*n < p → p ∣ normProduct n → p ∣ R) :
    2^(2 * factorialWeight n) ≤ 2^(11*n) * R := calc
  _ = (2 ^ factorialWeight n) ^ 2 := by rw [mul_comm 2 _, pow_mul]
  _ ≤ (inertFactor n)^2 := Nat.pow_le_pow_left (two_pow_weight_le n) 2
  _ ≤ primePowerOverhead n * R := inertFactor_sq_le_overhead_mul (by omega) hR hlarge
  _ ≤ _ := Nat.mul_le_mul_right _ (prime_power_overhead_le hn)

theorem large_prime_of_estimates {n : ℕ} (hn : 2^27 ≤ n)
    (hcert : 5700000 ≤ factorialWeight 1000000) :
    ∃ p : ℕ, p.Prime ∧ 2*n < p ∧ p ∣ normProduct n := by
  by_contra! h
  have hupper := weight_pow_le_mul_large_primes (R := 1) hn (by decide)
    (fun p hp hgt hpd => (h p hp hgt hpd).elim)
  rw [Nat.mul_one, Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at hupper
  exact (factorial_weight_large hn hcert).not_ge hupper

end Arxiv.«2607.05739»
