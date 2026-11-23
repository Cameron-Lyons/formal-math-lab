module

public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Primality

public section

namespace ThreeCubes114

/-- A fixed total coordinate sum fixes the product of the three pair sums. -/
theorem pair_sum_product (x y z k h : Int) (hk : x^3+y^3+z^3 = k)
    (hh : h = x+y+z) :
    h^3-k = 3*((x+y)*(y+z)*(z+x)) := by
  subst k h
  grind

/-- Conversely the sum and product constraints on the pair sums suffice. -/
theorem recover_from_pair_sums (a b c h k : Int) (hs : a+b+c=2*h)
    (hp : 3*(a*b*c) = h^3-k) :
    (h-a)^3+(h-b)^3+(h-c)^3 = k := by
  have hc : c = 2*h-a-b := by omega
  subst c
  grind

/-- After a divisor `c` has been chosen, the square test recovers `a,b`. -/
theorem pair_discriminant (a b c h : Int) (hs : a+b+c=2*h) :
    (2*h-c)^2 - 4*(a*b) = (a-b)^2 := by grind

/-- On this elliptic model the integer coordinates are `X = -ab`, `Y = a²b`. -/
theorem total_sum_fiber (a b c h t : Int) (hs : a+b+c=2*h) (ht : a*b*c=t) :
    (a^2*b)^2 + 2*h*(-a*b)*(a^2*b) + t*(a^2*b) = (-a*b)^3 := by
  subst t
  grind

/-- The other two nonzero pair sums satisfy `|a+b| ≤ |ab|+1`. This bounds
any one pair sum `c` from the fixed total and product. -/
theorem pair_bound_from_total (a b c h t : ℤ) (hs : a+b+c=2*h)
    (ht : a*b*c=t) (ht0 : t ≠ 0) :
    |c| * (|c| - 2*|h| - 1) ≤ |t| := by
  subst t
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp (left_ne_zero_of_mul ht0)
  have ha1 : 1 ≤ |a| := abs_pos.mpr ha
  have hb1 : 1 ≤ |b| := abs_pos.mpr hb
  have triangle := abs_sub (2*h) (a+b)
  rw [show 2*h-(a+b) = c by omega, abs_mul, abs_of_pos (by decide : (0:ℤ) < 2)] at triangle
  rw [abs_mul, abs_mul, mul_comm (|a| * |b|)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  nlinarith only [triangle, abs_add_le a b, mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)]

/-- One sufficiently large prime factor of `(h³−k)/3` excludes `h` as the
sum of the coordinates for every integer triple. No factorization of the
remaining cofactor and no coordinate-height bound are required. -/
theorem exclude_total_by_prime {p : ℕ} (hp : Nat.Prime p) {h k t : ℤ}
    (ht : 3*t=h^3-k) (ht0 : t ≠ 0) (hd : (p:ℤ) ∣ t)
    (hsize : |t| < (p:ℤ)*((p:ℤ)-2*|h|-1))
    (x y z : ℤ) (hh : x+y+z=h) : x^3+y^3+z^3 ≠ k := by
  intro hk
  have positive := pos_of_mul_pos_right ((abs_nonneg t).trans_lt hsize) (Int.natCast_nonneg p)
  have elim (a b c : ℤ) (hsum : a+b+c=2*h) (hprod : a*b*c=t) (hpc : (p:ℤ) ∣ c) : False := by
    have hc := right_ne_zero_of_mul (hprod ▸ ht0 : a*b*c ≠ 0)
    have hle := Int.le_of_dvd (abs_pos.mpr hc) ((dvd_abs _ _).mpr hpc)
    apply hsize.not_ge
    exact (mul_le_mul hle (by omega) positive.le (abs_nonneg c)).trans
      (pair_bound_from_total a b c h t hsum hprod ht0)
  have hprod : (x+y)*(y+z)*(z+x)=t := by
    have := pair_sum_product x y z k h hk hh.symm
    omega
  have prime := Nat.prime_iff_prime_int.mp hp
  rw [← hprod, prime.dvd_mul, prime.dvd_mul] at hd
  rcases hd with (ha | hb) | hc
  · exact elim (y+z) (z+x) (x+y) (by omega) (by grind) ha
  · exact elim (z+x) (x+y) (y+z) (by omega) (by grind) hb
  · exact elim (x+y) (y+z) (z+x) (by omega) hprod hc

/-- A total near 10²¹ excluded at all heights by a single prime. -/
theorem exclude_total_example (x y z : ℤ) (htot : x+y+z=1000000000000000000026) :
    x^3+y^3+z^3 ≠ 114 := by
  apply exclude_total_by_prime (p:=11784190164040280396372977175221259111273057)
    (t:=(1000000000000000000026^3-114)/3) _ (by decide) (by decide) (by decide)
    (by decide) x y z htot
  primality (cert := .witnesses [
    .lucas { root := 3, primeFactors := [2, 233, 1699877, 930725029187, 998975763799449176149] },
    .lucas { root := 2, primeFactors := [2, 43, 9883] },
    .lucas { root := 2, primeFactors := [2, 3, 61] },
    .lucas { root := 2, primeFactors := [2, 465362514593] },
    .lucas { root := 3, primeFactors := [2, 5351, 2717731] },
    .lucas { root := 11, primeFactors := [2, 5, 107] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 30197] },
    .lucas { root := 2, primeFactors := [2, 7549] },
    .lucas { root := 2, primeFactors := [2, 3, 17, 37] },
    .lucas { root := 2, primeFactors := [2, 3, 19, 31, 167, 653, 1296070896761] },
    .lucas { root := 3, primeFactors := [2, 5, 5011, 6466129] },
    .lucas { root := 2, primeFactors := [2, 3, 5, 167] },
    .lucas { root := 7, primeFactors := [2, 3, 23, 5857] },
    .lucas { root := 7, primeFactors := [2, 3, 61] }])

end ThreeCubes114
