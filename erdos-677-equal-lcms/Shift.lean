import PrimePowers

namespace Erdos677

open Finset

/-- Transport each prime power of a later entry to an earlier multiple, and take
their difference. This bounds the entry by divisibility, independently of the start. -/
theorem later_entry_dvd {n m k i D : ℕ} (hi : 0 < i) (hik : i ≤ k)
    (hd : n + k ≤ m) (hD : m ≤ n + D) (heq : lcmInterval m k = lcmInterval n k) :
    m + i ∣ lcmInterval 0 (D + i - 1) := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
  intro p e hp hq
  have hk : 0 < k := by omega
  have hr := (primePower_dvd_interval (n := m) hp hk).mpr
    ⟨m + i, by omega, by omega, hq⟩
  obtain ⟨x, hx, hx', hxq⟩ := (primePower_dvd_interval hp hk).mp (heq ▸ hr)
  apply (primePower_dvd_interval hp (by omega : 0 < D + i - 1)).mpr
  exact ⟨m + i - x, by omega, by omega, Nat.dvd_sub hq hxq⟩

/-- The last earlier entry also divides the LCM of the possible differences. -/
theorem earlier_end_dvd {n m k D : ℕ} (hk : 0 < k)
    (hd : n + k ≤ m) (hD : m ≤ n + D) (heq : lcmInterval m k = lcmInterval n k) :
    n + k ∣ lcmInterval 0 D := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
  intro p e hp hq
  have hl := (primePower_dvd_interval (n := n) hp hk).mpr
    ⟨n + k, by omega, le_rfl, hq⟩
  obtain ⟨x, hx, hx', hxq⟩ := (primePower_dvd_interval hp hk).mp (heq.symm ▸ hl)
  apply (primePower_dvd_interval hp (by omega : 0 < D)).mpr
  exact ⟨x - (n + k), by omega, by omega, Nat.dvd_sub hxq hq⟩

end Erdos677
