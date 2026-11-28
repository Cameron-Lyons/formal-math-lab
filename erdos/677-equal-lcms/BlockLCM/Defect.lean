module

public import PrimePowers
public import Mathlib.Data.Nat.ModEq

@[expose] public section

namespace Erdos677
open Finset

/-- Reflecting the earlier entries in the new endpoint sends them to the offsets
from 1 through k, preserving their common divisors with that endpoint. -/
private theorem gcd_next_eq_offset_gcd (n k : ℕ) :
    (lcmInterval n k).gcd (n+k+1) = (lcmInterval 0 k).gcd (n+k+1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [lcmInterval]
  apply Nat.dvd_antisymm <;> apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
  all_goals
    intro p e hp
    simp only [Nat.dvd_gcd_iff, primePower_dvd_interval hp hk, zero_add]
    rintro ⟨⟨x, hx, hx', hd⟩, hlast⟩
    exact ⟨⟨n+k+1-x, by omega, by omega, Nat.dvd_sub hlast hd⟩, hlast⟩

/-- The factors removed from a block product by taking its LCM can be
computed successively from the LCMs of the initial intervals. -/
theorem lcmInterval_mul_gcd_product (n k : ℕ) :
    lcmInterval n k * (∏ i ∈ range k, (lcmInterval 0 i).gcd (n+i+1)) =
      ∏ i ∈ range k, (n+i+1) := by
  induction k with
  | zero => simp [lcmInterval]
  | succ k ih =>
    -- The gcd at the new endpoint cancels the factor lost when taking its LCM.
    rw [prod_range_succ, prod_range_succ, mul_left_comm, lcmInterval_extend,
      ← gcd_next_eq_offset_gcd, Nat.lcm_mul_gcd, ← mul_assoc,
      mul_comm _ (lcmInterval n k), ih]

/-- Product of the five entries in a block. -/
def fiveBlockProduct (n : ℕ) := (n+1)*(n+2)*(n+3)*(n+4)*(n+5)

/-- Repeated factors in the product of five consecutive entries. -/
def fiveDefect (n : ℕ) := (Nat.gcd 2 (n+3)) * (Nat.gcd 6 (n+4)) * (Nat.gcd 12 (n+5))

theorem lcmInterval_five_mul_defect (n : ℕ) :
    lcmInterval n 5 * fiveDefect n = fiveBlockProduct n := by
  have h := lcmInterval_mul_gcd_product n 5
  simp only [prod_range_succ, prod_range_zero, Nat.one_mul, Nat.add_zero] at h
  change _ * (Nat.gcd 1 _ * Nat.gcd 1 _ * Nat.gcd 2 _ * Nat.gcd 6 _ * Nat.gcd 12 _) = _ at h
  simpa only [fiveDefect, fiveBlockProduct, Nat.gcd_one_left, Nat.one_mul] using h

theorem fiveDefect_mod_twelve (n : ℕ) : fiveDefect (n % 12) = fiveDefect n := by
  have common (d j : ℕ) (hd : d ∣ 12) :
      Nat.gcd d (n % 12 + j) = Nat.gcd d (n+j) := by
    simpa only [Nat.gcd_comm d] using (((Nat.mod_modEq n 12).of_dvd hd).add_right j).gcd_eq
  simp only [fiveDefect, common 2 3 (by decide), common 6 4 (by decide), common 12 5 (by decide)]

/-- To check a condition on two defects, it suffices to check starts modulo twelve. -/
theorem of_five_defect_residues {P : ℕ → ℕ → Prop}
    (table : ∀ i j : Fin 12, P (fiveDefect i) (fiveDefect j)) (n m : ℕ) :
    P (fiveDefect n) (fiveDefect m) := by
  simpa only [Fin.val_ofNat, fiveDefect_mod_twelve] using
    table (Fin.ofNat 12 n) (Fin.ofNat 12 m)

/-- Defects at starts 0 through 11, in order. -/
theorem fiveDefect_residue_table :
    (List.range 12).map fiveDefect = [2,12,6,8,6,12,2,24,6,4,6,24] := by decide

/-- A collision requires the repeated factors in the later product to increase. -/
theorem lcmInterval_five_strict_of_defect_le {n m : ℕ} (hnm : n < m)
    (hd : fiveDefect m ≤ fiveDefect n) : lcmInterval n 5 < lcmInterval m 5 := by
  have hp : fiveBlockProduct n < fiveBlockProduct m := by
    unfold fiveBlockProduct
    repeat first | apply Nat.mul_lt_mul_of_lt_of_lt | omega
  by_contra! h
  exact hp.not_ge (by simpa only [lcmInterval_five_mul_defect] using Nat.mul_le_mul h hd)

theorem lcmInterval_five_strict_of_mod_eq {n m : ℕ} (hnm : n < m) (hmod : n % 12 = m % 12) :
    lcmInterval n 5 < lcmInterval m 5 := by
  apply lcmInterval_five_strict_of_defect_le hnm
  rw [← fiveDefect_mod_twelve n, ← fiveDefect_mod_twelve m, hmod]

/-- Number of ordered residue pairs to which the strict-increase criterion applies. -/
theorem five_ordered_residue_count :
    (((range 12) ×ˢ (range 12)).filter
      (fun nm => fiveDefect nm.2 ≤ fiveDefect nm.1)).card = 87 := by decide

end Erdos677
