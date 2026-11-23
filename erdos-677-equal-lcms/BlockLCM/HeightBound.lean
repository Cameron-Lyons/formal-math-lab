import BlockLCM.Five
import BlockLCM.Scale
import BlockLCM.Slope
import Height

namespace Erdos677

open Finset

/-- Danesh and Bianchetti's height coordinate in §6.4, with
`r = bX-aY` and `s = Y-X`. For a collision, both are positive. -/
def fiveSlopeHeight (p : ℕ × ℕ) (n m : ℕ) : ℕ :=
  slopeHeight (p.2*(n+3) - p.1*(m+3)) (m-n)

private theorem ratio_bounds : ∀ p ∈ fiveRatios,
    0 < p.1 ∧ p.1 ≤ p.2 ∧ 4*(p.2-p.1)*(1+p.1)^3 ≤ 352 := by decide

/-- A bound on slope height gives an explicit bound on the earlier center.
This inequality applies to every product solution with one of the seven ratios. -/
theorem five_center_sq_le_height {p : ℕ × ℕ} (hp : p ∈ fiveRatios)
    {n m : ℕ} (hnm : n < m)
    (heq : (p.1 : ℤ) * fiveProduct (m+3) = p.2 * fiveProduct (n+3)) :
    (n+3)^2 ≤ 352 * (fiveSlopeHeight p n m)^3 := by
  obtain ⟨ha, hab, hconst⟩ := ratio_bounds p hp
  have hxy := Nat.add_lt_add_right hnm 3
  obtain ⟨hslope, hscale⟩ := five_scale_bound (by omega : 3 ≤ n+3) hxy ha hab
    (by simpa [fiveProduct] using heq)
  have hden := five_reduced_center_le (by omega : 0 < n+3) hxy hslope
  simp only [Nat.add_sub_add_right] at hden
  calc
    (n+3)^2 ≤ 4*(p.2-p.1)*((n+3) / (n+3).gcd (m+3))^3 := hscale
    _ ≤ 4*(p.2-p.1)*((1+p.1)*fiveSlopeHeight p n m)^3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hden 3)
    _ = (4*(p.2-p.1)*(1+p.1)^3)*(fiveSlopeHeight p n m)^3 := by simp only [mul_pow, mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ hconst

/-- Any disjoint equal-LCM pair of length five would survive the seven-curve
reduction only at naive slope height greater than three trillion. -/
theorem five_collision_requires_large_height {n m : ℕ} (hd : n+5 ≤ m)
    (heq : lcmInterval m 5 = lcmInterval n 5) :
    3 * 10^12 < fiveSlopeHeight (fiveRatio n m) n m := by
  have hnm : n < m := by omega
  have hp := fiveRatio_mem_of_collision hnm heq
  have hprod := (five_collision_iff_product n m).mp heq
  have hn : 10^20 < n := lt_of_not_ge fun h => no_collision_five_six (Or.inl rfl) hd h heq
  apply (Nat.pow_lt_pow_iff_left (by decide : 3 ≠ 0)).mp
  apply Nat.lt_of_mul_lt_mul_left (a := 352)
  calc
    352 * (3 * 10^12)^3 < (10^20)^2 := by decide
    _ ≤ (n+3)^2 := Nat.pow_le_pow_left (by omega) 2
    _ ≤ _ := five_center_sq_le_height hp hnm hprod

/-- The disjoint length-five case throughout the specified slope-height range,
with no bound on either starting parameter. -/
theorem erdos_677_five_of_height_le {m n : ℕ} (hd : n+5 ≤ m)
    (hh : fiveSlopeHeight (fiveRatio n m) n m ≤ 3 * 10^12) :
    lcmInterval m 5 ≠ lcmInterval n 5 :=
  fun heq => (Nat.not_lt_of_ge hh) (five_collision_requires_large_height hd heq)

end Erdos677
