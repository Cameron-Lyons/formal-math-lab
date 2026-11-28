module

public import ArctanLargePrime

public section

namespace Arxiv.«2607.05739»

/-- An integer value forces every prime factor of the norm above 2n to divide
1 + m². The factorial estimate then gives an explicit exponential lower bound. -/
theorem exp_bound_of_estimates {n : ℕ} {m : ℤ} (hn : 2^27 ≤ n)
    (hcert : 5700000 ≤ factorialWeight 1000000) (h : B n = A n * m) :
    2^(n / 4) ≤ 1 + m.natAbs^2 := by
  have hupper := weight_pow_le_mul_large_primes (R := 1 + m.natAbs^2) hn (by positivity)
    (fun p hp hgt hd => by
      have hpd := prime_dvd_one_add_sq_of_integerValue hp hd
        (not_sq_dvd_normProduct_of_large_prime hp hgt hd) h
      exact_mod_cast (show (p : ℤ) ∣ ((1 + m.natAbs^2 : ℕ) : ℤ) by simpa using hpd))
  have hw := (Nat.mul_le_mul_left (n / 1000000) hcert).trans (weight_blocks n 1000000)
  have he : 11*n + n/4 ≤ 2*factorialWeight n := by omega
  have hlower := (Nat.pow_le_pow_right (by decide : 0 < 2) he).trans hupper
  rw [pow_add] at hlower
  exact Nat.le_of_mul_le_mul_left hlower (pow_pos (by decide) _)

end Arxiv.«2607.05739»
