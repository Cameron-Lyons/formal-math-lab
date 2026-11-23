import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.LinearCombination

namespace Erdos677

/-- A rational slope `R/S = (bX-aY)/(Y-X)` constrains the denominator of the
reduced center ratio `Y/X`. The equation suffices for any positive choice of
`R,S`, in particular the coprime coordinates used for naive height. -/
theorem five_slope_denom_dvd {X Y a b R S : ℕ} (hX : 0 < X)
    (hslope : ((b : ℤ) * X - a * Y) * S = ((Y : ℤ) - X) * R) :
    X / X.gcd Y ∣ R + a * S := by
  have hz : ((R : ℤ) + b * S) * X = (R + (a : ℤ) * S) * Y := by
    linear_combination hslope
  have hn : (R + b * S) * X = (R + a * S) * Y := by exact_mod_cast hz
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left ..) (Nat.gcd_pos_of_pos_left _ hX),
    mul_comm (X.gcd Y), ← Nat.gcd_mul_left]
  apply Nat.dvd_gcd (Nat.dvd_mul_left ..)
  rw [← hn]
  exact Nat.dvd_mul_left ..

/-- The naive height of the rational number `r/s` in lowest terms. -/
def slopeHeight (r s : ℕ) : ℕ :=
  max (r / r.gcd s) (s / r.gcd s)

/-- For the manuscript coordinate `r/s = (bX-aY)/(Y-X)`, each reduced
coordinate is at most its height. Reconstructing the center ratio gives a
bound on its reduced denominator. -/
theorem five_reduced_center_le {X Y a b : ℕ} (hX : 0 < X) (hXY : X < Y)
    (hpos : a * Y < b * X) :
    X / X.gcd Y ≤ (1 + a) * slopeHeight (b*X-a*Y) (Y-X) := by
  let r := b*X-a*Y
  let s := Y-X
  let g := r.gcd s
  let R := r/g
  let S := s/g
  have hr : 0 < r := Nat.sub_pos_of_lt hpos
  have hg : 0 < g := Nat.gcd_pos_of_pos_left s hr
  have cross : r * S = s * R := by
    change r * (s / g) = s * (r / g)
    rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_right r s),
      ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left r s), mul_comm r s]
  have hslope : ((b : ℤ) * X - a * Y) * S = ((Y : ℤ) - X) * R := by
    rw [← Nat.cast_mul b X, ← Nat.cast_mul a Y, ← Nat.cast_sub hpos.le, ← Nat.cast_sub hXY.le]
    exact_mod_cast cross
  have hR : 0 < R := Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_left r s)) hg
  have hbound := Nat.le_of_dvd (show 0 < R+a*S by omega) (five_slope_denom_dvd hX hslope)
  calc
    _ ≤ R+a*S := hbound
    _ ≤ max R S + a * max R S :=
      Nat.add_le_add (le_max_left ..) (Nat.mul_le_mul_left a (le_max_right ..))
    _ = (1+a) * slopeHeight r s := by simp [slopeHeight, R, S, g, add_mul]

end Erdos677
