import BinomialBounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Erdos677

open Finset

/-- The LCM differs from its binomial lower divisor by a positive integer
dividing a constant that depends only on the block length. -/
theorem exists_interval_factor {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ∃ t, 0 < t ∧ t ∣ lcmInterval 0 k / k ∧
      lcmInterval n k = k * (n + k).choose k * t := by
  obtain ⟨t, ht⟩ := choose_mul_dvd_interval n k hk
  have hpos : 0 < lcmInterval n k :=
    Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr fun x hx => (mem_Ioc.mp hx).1.ne_bot)
  have hdiv := interval_dvd_lcm_mul_choose n k
  rw [ht, show k * (n+k).choose k * t = (k * t) * (n+k).choose k by ac_rfl] at hdiv
  exact ⟨t, by by_contra! h; simp [show t = 0 by omega, ht] at hpos,
    Nat.dvd_div_of_mul_dvd (Nat.dvd_of_mul_dvd_mul_right (Nat.choose_pos (by omega)) hdiv), ht⟩

private theorem choose_strict {n m k : ℕ} (hk : 0 < k) (hnm : n < m) :
    (n + k).choose k < (m + k).choose k := by
  cases k with
  | zero => omega
  | succ j =>
    apply lt_of_lt_of_le _ (Nat.choose_le_choose (j+1) (show (n+(j+1))+1 ≤ m+(j+1) by omega))
    rw [Nat.choose_succ_succ]
    exact Nat.lt_add_of_pos_left (Nat.choose_pos (by omega))

/-- An equal-LCM pair gives an exact ratio of binomial coefficients. Both
multipliers divide the same length-dependent integer. -/
theorem equal_choose_ratio {n m k : ℕ} (hk : 0 < k) (hnm : n < m)
    (heq : lcmInterval m k = lcmInterval n k) :
    ∃ u v, 0 < v ∧ v < u ∧ u ∣ lcmInterval 0 k / k ∧ v ∣ lcmInterval 0 k / k ∧
      v * (m + k).choose k = u * (n + k).choose k := by
  obtain ⟨u, hu, hdu, heu⟩ := exists_interval_factor hk n
  obtain ⟨v, hv, hdv, hev⟩ := exists_interval_factor hk m
  have hmul : v * (m + k).choose k = u * (n + k).choose k :=
    Nat.eq_of_mul_eq_mul_left hk (by simpa [hev, heu, mul_assoc, mul_comm, mul_left_comm] using heq)
  refine ⟨u, v, hv, ?_, hdu, hdv, hmul⟩
  by_contra! h
  have hle := Nat.mul_le_mul_right ((n + k).choose k) h
  have hlt := Nat.mul_lt_mul_of_pos_left (choose_strict hk hnm) hv
  omega

/-- The integer polynomial with roots at the offsets of a length-`k` block,
using twice the center to allow even block lengths. -/
def centeredProduct (k : ℕ) (x : ℤ) : ℤ :=
  ∏ i ∈ range k, (x + (k : ℤ) - (2 * (i : ℤ) + 1))

theorem centeredProduct_at_center (n k : ℕ) :
    centeredProduct k (2 * (n : ℤ) + k + 1) =
      (2 : ℤ) ^ k * ↑((n + k).descFactorial k) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  calc
    centeredProduct k (2 * (n : ℤ) + k + 1) =
        ∏ i ∈ range k, 2 * (↑(n + k - i) : ℤ) := by
      apply prod_congr rfl
      intro i hi
      have h := mem_range.mp hi
      rw [Nat.cast_sub (by omega), Nat.cast_add]
      ring
    _ = _ := by simp [prod_mul_distrib]

/-- For fixed positive length, a collision must solve one of finitely many
integer polynomial equations between the two doubled centers. -/
theorem equal_centered_ratio {n m k : ℕ} (hk : 0 < k) (hnm : n < m)
    (heq : lcmInterval m k = lcmInterval n k) :
    ∃ u v : ℕ, 0 < v ∧ v < u ∧ u ∣ lcmInterval 0 k / k ∧ v ∣ lcmInterval 0 k / k ∧
      (v : ℤ) * centeredProduct k (2 * (m : ℤ) + k + 1) =
      (u : ℤ) * centeredProduct k (2 * (n : ℤ) + k + 1) := by
  obtain ⟨u, v, hv, hvu, hdu, hdv, h⟩ := equal_choose_ratio hk hnm heq
  refine ⟨u, v, hv, hvu, hdu, hdv, ?_⟩
  simp only [centeredProduct_at_center, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hh : (v : ℤ) * ↑((m + k).choose k) = (u : ℤ) * ↑((n + k).choose k) := by exact_mod_cast h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z : ℤ => 2^k * k.factorial * z) hh

theorem centeredProduct_five (x : ℤ) :
    centeredProduct 5 x = x * (x^2 - 4) * (x^2 - 16) := by
  norm_num [centeredProduct, Finset.prod_range_succ]
  ring

theorem centeredProduct_six (x : ℤ) :
    centeredProduct 6 x = (x^2 - 1) * (x^2 - 9) * (x^2 - 25) := by
  norm_num [centeredProduct, Finset.prod_range_succ]
  ring

theorem factor_constant_five : lcmInterval 0 5 / 5 = (12 : ℕ) := by decide

theorem factor_constant_six : lcmInterval 0 6 / 6 = (10 : ℕ) := by decide

private theorem five_six_centered_bounds {k : ℕ} (hk : k = 5 ∨ k = 6) {x B : ℤ}
    (hx : 6 ≤ x) (hB : 0 ≤ B) (hBx : B ≤ x) :
    (B^2 - 35) * x^k ≤ B^2 * centeredProduct k x ∧ centeredProduct k x ≤ x^k := by
  have hx' : 0 ≤ x := by omega
  have h36 : 36 ≤ x^2 := by
    nlinarith [mul_nonneg (show 0 ≤ x-6 by omega) (show 0 ≤ x+6 by omega)]
  have hdiff : 0 ≤ x^2 - B^2 := by
    nlinarith [mul_nonneg (show 0 ≤ x-B by omega) (show 0 ≤ x+B by omega)]
  rcases hk with rfl | rfl
  · rw [centeredProduct_five]
    constructor
    · calc
        (B^2 - 35) * x^5 ≤ B^2 * (x^3 * (x^2 - 35)) := by
          nlinarith [mul_nonneg (show 0 ≤ 35*x^3 by positivity) hdiff]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [show 0 ≤ x^3 by positivity]) (sq_nonneg B)
    · nlinarith [mul_nonneg hx' (show 0 ≤ 20*x^2 - 64 by omega)]
  · rw [centeredProduct_six]
    constructor
    · calc
        (B^2 - 35) * x^6 ≤ B^2 * (x^4 * (x^2 - 35)) := by
          nlinarith [mul_nonneg (show 0 ≤ 35*x^4 by positivity) hdiff]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg B)
    · nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 35*x^2 - 259 by omega)]

/-- Exact integer bounds suitable for a dyadic search at lengths five and six.
`B` may be the lower endpoint of any range containing the earlier doubled center. -/
theorem five_six_power_envelope {n m k : ℕ} (hk : k = 5 ∨ k = 6) (hnm : n < m)
    (heq : lcmInterval m k = lcmInterval n k) :
    ∃ u v : ℕ, 0 < v ∧ v < u ∧ u ∣ lcmInterval 0 k / k ∧ v ∣ lcmInterval 0 k / k ∧
      ∀ B : ℤ, 0 ≤ B → B ≤ 2*(n:ℤ)+k+1 →
        ((u:ℤ)*(B^2-35))*(2*(n:ℤ)+k+1)^k ≤ (v:ℤ)*B^2*(2*(m:ℤ)+k+1)^k ∧
        ((v:ℤ)*(B^2-35))*(2*(m:ℤ)+k+1)^k ≤ (u:ℤ)*B^2*(2*(n:ℤ)+k+1)^k := by
  obtain ⟨u, v, hv, hvu, hdu, hdv, hp⟩ := equal_centered_ratio (by omega) hnm heq
  refine ⟨u, v, hv, hvu, hdu, hdv, ?_⟩
  intro B hB hBX
  let X : ℤ := 2*(n:ℤ)+k+1
  let Y : ℤ := 2*(m:ℤ)+k+1
  change (v:ℤ)*centeredProduct k Y = (u:ℤ)*centeredProduct k X at hp
  have hX : 6 ≤ X := by dsimp [X]; omega
  have hY : X ≤ Y := by dsimp [X,Y]; omega
  have hPX := five_six_centered_bounds hk hX hB hBX
  have hPY := five_six_centered_bounds hk (hX.trans hY) hB (hBX.trans hY)
  have bound {x y a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hl : (B^2-35)*x^k ≤ B^2*centeredProduct k x)
      (hu : centeredProduct k y ≤ y^k)
      (eq : a*centeredProduct k x = b*centeredProduct k y) :
      (a*(B^2-35))*x^k ≤ b*B^2*y^k := by
    calc
      (a*(B^2-35))*x^k = a*((B^2-35)*x^k) := by ring
      _ ≤ a*(B^2*centeredProduct k x) := mul_le_mul_of_nonneg_left hl ha
      _ = B^2*(a*centeredProduct k x) := by ring
      _ = (b*B^2)*centeredProduct k y := by rw [eq]; ring
      _ ≤ (b*B^2)*y^k := mul_le_mul_of_nonneg_left hu (mul_nonneg hb (sq_nonneg B))
  exact ⟨bound (by positivity) (by positivity) hPX.1 hPY.2 hp.symm,
         bound (by positivity) (by positivity) hPY.1 hPX.2 hp⟩

/-- The power envelope has a pair of relatively prime multipliers. This removes
duplicate slopes when enumerating the divisors permitted at either length. -/
theorem five_six_reduced_envelope {n m k : ℕ} (hk : k = 5 ∨ k = 6) (hnm : n < m)
    (heq : lcmInterval m k = lcmInterval n k) :
    ∃ u v : ℕ, 0 < v ∧ v < u ∧ u ∣ lcmInterval 0 k / k ∧ v ∣ lcmInterval 0 k / k ∧
      u.Coprime v ∧ ∀ B : ℤ, 0 ≤ B → B ≤ 2*(n:ℤ)+k+1 →
        ((u:ℤ)*(B^2-35))*(2*(n:ℤ)+k+1)^k ≤ (v:ℤ)*B^2*(2*(m:ℤ)+k+1)^k ∧
        ((v:ℤ)*(B^2-35))*(2*(m:ℤ)+k+1)^k ≤ (u:ℤ)*B^2*(2*(n:ℤ)+k+1)^k := by
  obtain ⟨u, v, hv, hvu, hdu, hdv, env⟩ := five_six_power_envelope hk hnm heq
  let g := u.gcd v
  have hg : 0 < g := Nat.gcd_pos_of_pos_right u hv
  have hgu : g ∣ u := Nat.gcd_dvd_left ..
  have hgv : g ∣ v := Nat.gcd_dvd_right ..
  have hlt : v/g < u/g := (mul_lt_mul_iff_of_pos_left hg).mp
    (by simpa only [Nat.mul_div_cancel' hgv, Nat.mul_div_cancel' hgu] using hvu)
  refine ⟨u/g, v/g, Nat.div_pos (Nat.le_of_dvd hv hgv) hg, hlt,
    (Nat.div_dvd_of_dvd hgu).trans hdu, (Nat.div_dvd_of_dvd hgv).trans hdv,
    Nat.coprime_div_gcd_div_gcd hg, ?_⟩
  have cancel {a b : ℕ} (ha : g ∣ a) (hb : g ∣ b) {x y : ℤ}
      (h : (a : ℤ)*x ≤ (b : ℤ)*y) : (↑(a/g) : ℤ)*x ≤ (↑(b/g) : ℤ)*y := by
    apply le_of_mul_le_mul_left (a := (g : ℤ)) _ (by exact_mod_cast hg)
    simpa only [← mul_assoc, ← Int.natCast_mul, Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb] using h
  intro B hB hBX
  obtain ⟨h₁, h₂⟩ := env B hB hBX
  rw [mul_assoc, mul_assoc (v : ℤ)] at h₁
  rw [mul_assoc, mul_assoc (u : ℤ)] at h₂
  simpa only [mul_assoc] using And.intro (cancel hgu hgv h₁) (cancel hgv hgu h₂)

end Erdos677
