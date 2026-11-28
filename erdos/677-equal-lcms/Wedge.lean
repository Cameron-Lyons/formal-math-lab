module

public import FixedLength

@[expose] public section

namespace Erdos677

/-- Combine bounds on two scaled powers to compare their products without taking roots. -/
private theorem chain_power_bounds {k : ℕ} {a b c d x y : ℤ} (hk : 0 < k)
    (ha : 0 < a) (hd : 0 ≤ d) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (first : a*b^k ≤ c*d^k) (second : c*x^k ≤ a*y^k) : b*x ≤ d*y := by
  apply le_of_pow_le_pow_left₀ hk.ne' (mul_nonneg hd hy)
  apply le_of_mul_le_mul_left (a := a) _ ha
  calc
    a * (b*x)^k = (a*b^k)*x^k := by rw [mul_pow]; ring
    _ ≤ (c*d^k)*x^k := mul_le_mul_of_nonneg_right first (pow_nonneg hx k)
    _ = (c*x^k)*d^k := by ring
    _ ≤ (a*y^k)*d^k := mul_le_mul_of_nonneg_right second (pow_nonneg hd k)
    _ = a * (d*y)^k := by rw [mul_pow]; ring

/-- A certified slope p/q traps the integer qY−pX in a finite interval
throughout the dyadic block L ≤ X < 2L. -/
theorem determinant_bounds {k : ℕ} {u v L p q E X Y : ℤ}
    (hk : 0 < k) (_hu : 0 ≤ u) (hv : 0 < v) (hL : 0 < L) (hp : 0 ≤ p)
    (hq : 0 < q) (hE : 0 ≤ E) (hY : 0 ≤ Y) (h35 : 35 < L^2)
    (hXL : L ≤ X) (hXU : X < 2*L)
    (envLo : u*(L^2-35)*X^k ≤ v*L^2*Y^k)
    (envHi : v*(L^2-35)*Y^k ≤ u*L^2*X^k)
    (slopeLo : v*L^2*(max 0 (p*L-E))^k ≤ u*(L^2-35)*(q*L)^k)
    (slopeHi : u*L^2*(q*L)^k ≤ v*(L^2-35)*(p*L+E)^k) :
    -(2*E) ≤ q*Y-p*X ∧ q*Y-p*X ≤ 2*E := by
  have hX : 0 ≤ X := hL.le.trans hXL
  have hqL : 0 ≤ q*L := mul_nonneg hq.le hL.le
  have hlo := chain_power_bounds hk (mul_pos hv (sq_pos_of_pos hL)) hqL hX hY slopeLo envLo
  have hhi := chain_power_bounds hk (mul_pos hv (sub_pos.mpr h35)) hX hqL
    (add_nonneg (mul_nonneg hp hL.le) hE) envHi slopeHi
  have hleft := (mul_le_mul_of_nonneg_right (le_max_right 0 (p*L-E)) hX).trans hlo
  have hEX := mul_le_mul_of_nonneg_left hXU.le hE
  constructor <;> apply le_of_mul_le_mul_right (a := L) _ hL
  · nlinarith only [hleft, hEX]
  · nlinarith only [hhi, hEX]

end Erdos677
