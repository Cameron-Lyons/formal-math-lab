module

public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Nat

@[expose] public section

namespace Erdos677

private theorem five_slope {x y a b : ℤ} (hx : 3 ≤ x) (hxy : x < y) (ha : 0 < a)
    (hprod : a * (y * (y^2-1) * (y^2-4)) = b * (x * (x^2-1) * (x^2-4))) :
    a*y < b*x := by
  have hx4 : 4 < x^2 := by nlinarith [sq_nonneg (x - 3)]
  have hsq : x^2 < y^2 := by gcongr
  have hay : 0 < a*y := mul_pos ha (by omega)
  have hfactor : 0 < (x^2-1)*(x^2-4) := mul_pos (by omega) (by omega)
  apply (mul_lt_mul_iff_left₀ hfactor).mp
  calc
    a*y * ((x^2-1)*(x^2-4)) < a*y * ((y^2-1)*(y^2-4)) := by gcongr; omega
    _ = b*x * ((x^2-1)*(x^2-4)) := by linear_combination hprod

/-- A repeated five-term product forces a divisor-square bound on the common scale. -/
theorem five_scale_int {c u v a b : ℤ} (hc : 0 < c) (huv : u < v)
    (hx : 3 ≤ c*u) (ha : 0 < a)
    (heq : a * ((c*v) * ((c*v)^2-1) * ((c*v)^2-4)) =
           b * ((c*u) * ((c*u)^2-1) * ((c*u)^2-4))) :
    a*v < b*u ∧ c^2 ≤ 4*(b-a)*u := by
  have hslope := five_slope hx (mul_lt_mul_of_pos_left huv hc) ha heq
  have hs : a*v < b*u := (mul_lt_mul_iff_right₀ hc).mp (by
    simpa only [mul_left_comm, mul_assoc] using hslope)
  refine ⟨hs, ?_⟩
  have hd : c^2 ∣ 4*(b*u-a*v) := by
    refine ⟨c^2*(a*v^5-b*u^5) - 5*(a*v^3-b*u^3), ?_⟩
    apply mul_left_cancel₀ hc.ne'
    linear_combination -heq
  have hle := Int.le_of_dvd (show 0 < 4*(b*u-a*v) by omega) hd
  linarith [mul_lt_mul_of_pos_left huv ha]

/-- Squaring the earlier center bounds it in terms of the denominator of the reduced
ratio of the centers and the difference of the multipliers. -/
theorem five_scale_bound {x y a b : ℕ} (hx : 3 ≤ x) (hxy : x < y) (ha : 0 < a)
    (hab : a ≤ b)
    (heq : (a : ℤ) * ((y : ℤ) * ((y : ℤ)^2-1) * ((y : ℤ)^2-4)) =
           (b : ℤ) * ((x : ℤ) * ((x : ℤ)^2-1) * ((x : ℤ)^2-4))) :
    a*y < b*x ∧ x^2 ≤ 4*(b-a)*(x / x.gcd y)^3 := by
  obtain ⟨c, u, v, hc, huv_coprime, rfl, rfl⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_left y (by omega : 0 < x))
  rw [mul_comm u c, mul_comm v c] at *
  simp only [Nat.gcd_mul_left, huv_coprime.gcd_eq_one, Nat.mul_one, Nat.mul_div_cancel_left _ hc]
  have huv : u < v := Nat.lt_of_mul_lt_mul_left hxy
  obtain ⟨hslope, hscale⟩ := five_scale_int (c := (c : ℤ)) (u := (u : ℤ)) (v := (v : ℤ))
    (a := (a : ℤ)) (b := (b : ℤ)) (by exact_mod_cast hc) (by exact_mod_cast huv)
    (by exact_mod_cast hx) (by exact_mod_cast ha) (by simpa only [Nat.cast_mul] using heq)
  rw [← Nat.cast_sub hab] at hscale
  norm_cast at hslope hscale
  constructor
  · simpa only [Nat.mul_left_comm] using Nat.mul_lt_mul_of_pos_left hslope hc
  · calc
      (c*u)^2 = c^2*u^2 := mul_pow ..
      _ ≤ (4*(b-a)*u)*u^2 := Nat.mul_le_mul_right _ hscale
      _ = _ := by ring

end Erdos677
