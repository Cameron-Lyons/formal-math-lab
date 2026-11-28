module

public import ArctanPrimeInterval
import Mathlib.Tactic.Primality

public section

namespace Arxiv.«2607.05739»

private theorem large_prime_witness {k n p : ℕ} (hp : p.Prime) (he : k^2 + 1 = p)
    (hkn : k ≤ n) (hpn : 2*n < p) :
    ∃ p : ℕ, p.Prime ∧ 2*n < p ∧ p ∣ normProduct n :=
  ⟨p, hp, hpn, (prime_once_on_interval hp he hkn (by omega)).1⟩

/-- Seven overlapping intervals have a prime of the form k²+1 exceeding 2n.
The larger primality claims use Lucas certificates. -/
theorem exists_large_prime_small {n : ℕ} (hn : 4 ≤ n) (hlt : n < 2^36) :
    ∃ p : ℕ, p.Prime ∧ 2*n < p ∧ p ∣ normProduct n := by
  by_cases h₁ : n < 6
  · exact large_prime_witness (p := 17) (k := 4) (by decide) (by decide) hn (by omega)
  by_cases h₂ : n < 10
  · exact large_prime_witness (p := 37) (k := 6) (by decide) (by decide) (by omega) (by omega)
  by_cases h₃ : n < 36
  · exact large_prime_witness (p := 101) (k := 10) (by decide) (by decide) (by omega) (by omega)
  by_cases h₄ : n < 536
  · exact large_prime_witness (p := 1297) (k := 36)
      (by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2,3] }]))
      (by decide) (by omega) (by omega)
  by_cases h₅ : n < 16404
  · exact large_prime_witness (p := 287297) (k := 536)
      (by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2,67] }]))
      (by decide) (by omega) (by omega)
  by_cases h₆ : n < 370730
  · exact large_prime_witness (p := 269091217) (k := 16404)
      (by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2,3,1367] },
        .lucas { root := 5, primeFactors := [2,683] }]))
      (by decide) (by omega) (by omega)
  exact large_prime_witness (p := 137440732901) (k := 370730)
    (by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2,5,131,283] }]))
    (by decide) (by omega) (by omega)

end Arxiv.«2607.05739»
