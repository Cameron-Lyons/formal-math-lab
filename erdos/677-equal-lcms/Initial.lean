module

public import PrimePowers
public import FormalBook.Chapter_03.Sylvester
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public section

namespace Erdos677
open Finset

/-- A block with only prime factors at most its length cannot share its LCM with
a block of that length whose entries all exceed the length. -/
theorem smooth_block_ne {n k m : ℕ} (hk : 0 < k) (hm : k ≤ m)
    (hsmooth : ∀ x, n < x → x ≤ n + k → ∀ p : ℕ, p.Prime → p ∣ x → p ≤ k) :
    lcmInterval m k ≠ lcmInterval n k := by
  obtain ⟨p, hkp, hp, hd⟩ :=
    chapter3.Sylvester.exists_prime_gt_dvd_choose k (m + k) (by omega) hk
  have hprod : p ∣ (m + k).descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact hd.trans (dvd_mul_left ..)
  rw [Nat.descFactorial_eq_prod_range] at hprod
  obtain ⟨i, hi, hpi⟩ := hp.prime.exists_mem_finset_dvd hprod
  have hi' := mem_range.mp hi
  have hright : p ^ 1 ∣ lcmInterval m k :=
    (primePower_dvd_interval hp hk).mpr
      ⟨m + k - i, by omega, by omega, by simpa using hpi⟩
  intro heq
  rw [heq] at hright
  obtain ⟨x, hx, hx', hpx⟩ := (primePower_dvd_interval hp hk).mp hright
  exact hkp.not_ge (hsmooth x hx hx' p hp (by simpa using hpx))

/-- The first block starting at 1 has a different LCM from every disjoint later
block of the same length. -/
theorem first_block_ne {k m : ℕ} (hk : 0 < k) (hdis : k ≤ m) :
    lcmInterval m k ≠ lcmInterval 0 k := by
  apply smooth_block_ne hk hdis
  intro x hx hx' p _ hpx
  exact (Nat.le_of_dvd hx hpx).trans (by simpa using hx')

end Erdos677
