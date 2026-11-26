module

public import PrimePowers
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Erdos677
open Finset

def lineLCM (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (lineLCM n k).lcm (n + k + 1)

private theorem lineLCM_eq (n k : ℕ) : lineLCM n k = lcmInterval n k := by
  induction k with
  | zero => simp [lineLCM, lcmInterval]
  | succ k ih => rw [lineLCM, ih, lcmInterval_extend]

private theorem interval_dvd_product (n k : ℕ) :
    lcmInterval n k ∣ (n + 1).ascFactorial k := by
  induction k with
  | zero => simp [lcmInterval]
  | succ k ih =>
    rw [lcmInterval_extend, Nat.ascFactorial_succ, show n + 1 + k = n + k + 1 by omega]
    exact Nat.lcm_dvd (Nat.dvd_mul_left_of_dvd ih _) (dvd_mul_right ..)

def linePoint (k : ℕ) (x y : ℤ) : Bool :=
  let n := ((x - k - 1) / 2).toNat
  let m := ((y - k - 1) / 2).toNat
  if x = 2 * (n : ℤ) + k + 1 ∧ y = 2 * (m : ℤ) + k + 1 ∧ 0 < k ∧ n + k ≤ m then
    if (n + 1).ascFactorial k % (m + 1) = 0 then decide (lineLCM m k ≠ lineLCM n k)
    else true
  else true

def lineStart (L q z : ℕ) (h : ℤ) : ℤ := L + (- (z : ℤ) * h - L) % q

/-- Verify all compatible integer centers on the line `q*y - p*x = h` with
`L ≤ x < 2*L`. Here `z` is an inverse of `p` modulo `q`. -/
def checkLine (k L p q z : ℕ) (h : ℤ) : Bool :=
  let first := lineStart L q z h
  let count := ((2 * (L : ℤ) - 1 - first) / q + 1).toNat
  (List.range count).all fun i =>
    let x := first + (i : ℤ) * q
    linePoint k x (((p : ℤ) * x + h) / q)

theorem checkLine_sound {k L p q z n m : ℕ} {h : ℤ}
    (hc : checkLine k L p q z h = true) (hq : 0 < q)
    (hinv : (p : ℤ) * z ≡ 1 [ZMOD (q : ℤ)])
    (hk : 0 < k) (hd : n + k ≤ m)
    (hlo : (L : ℤ) ≤ 2 * (n : ℤ) + k + 1)
    (hhi : 2 * (n : ℤ) + k + 1 < 2 * (L : ℤ))
    (hdet : h = (q : ℤ) * (2 * (m : ℤ) + k + 1) - p * (2 * (n : ℤ) + k + 1)) :
    lcmInterval m k ≠ lcmInterval n k := by
  let x := 2 * (n : ℤ) + k + 1
  let y := 2 * (m : ℤ) + k + 1
  have hxl : (L : ℤ) ≤ x := hlo
  have hxu : x < 2 * (L : ℤ) := hhi
  have hxy : h = (q : ℤ) * y - p * x := hdet
  have hqz : 0 < (q : ℤ) := by exact_mod_cast hq
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hinv
  have hres : x - L ≡ -(z : ℤ) * h - L [ZMOD (q : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    use -(z : ℤ) * y - t * x
    rw [hxy]
    linear_combination -x * ht
  let i := ((x - L) / q).toNat
  have hi : (i : ℤ) = (x - L) / q := Int.toNat_of_nonneg
    (Int.ediv_nonneg (by omega) hqz.le)
  have hsplit := Int.emod_add_mul_ediv (x - L) q
  rw [show (x - L) % q = (-(z : ℤ) * h - L) % q from hres, ← hi] at hsplit
  have he : lineStart L q z h + (i : ℤ) * q = x := by
    unfold lineStart
    linarith [mul_comm (i : ℤ) (q : ℤ)]
  have hb : (i : ℤ) ≤ (2 * (L : ℤ) - 1 - lineStart L q z h) / q :=
    (Int.le_ediv_iff_mul_le hqz).2 (by omega)
  have hiMem : i ∈ List.range (((2 * (L : ℤ) - 1 - lineStart L q z h) / q + 1).toNat) :=
    List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp hc i hiMem
  change linePoint k _ _ = true at hh
  rw [he] at hh
  have hy : ((p : ℤ) * x + h) / q = y := by
    rw [hxy, show (p : ℤ) * x + ((q : ℤ) * y - p * x) = y * q by ring]
    exact Int.mul_ediv_cancel _ hqz.ne'
  rw [hy] at hh
  have hn : ((x - k - 1) / 2).toNat = n := by dsimp [x]; omega
  have hm : ((y - k - 1) / 2).toNat = m := by dsimp [y]; omega
  intro heq
  have hfirst : m + 1 ∣ lcmInterval m k :=
    Finset.dvd_lcm (f := id) (mem_Ioc.mpr ⟨by omega, by omega⟩)
  have hzero := Nat.mod_eq_zero_of_dvd ((heq ▸ hfirst).trans (interval_dvd_product n k))
  simp [linePoint, hn, hm, x, y, hk, hd, hzero, lineLCM_eq, heq] at hh

end Erdos677
