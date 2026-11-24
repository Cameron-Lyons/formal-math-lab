module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

public section

namespace SmallCubic.TwoPoint.PrimaryTwo

/-- Each row encodes the coefficients of the 23 correction variables in bits
0 through 22 and the right-hand side in bit 23. The variable order is
x,y,z, and, within each, the positive-degree coefficients of P then Q.
The Python checker derives these row subsets for every compatible odd-x endpoint residue modulo 4. -/
def contradictorySubsystems : Array (List ℕ) := #[
  [8, 32768, 8421384],
  [8192, 8226, 32768, 565256, 2261000, 11182114],
  [8192, 8226, 32768, 8953864, 10649608, 11182114],
  [8192, 32768, 565256, 8396834, 10649608, 11182114],
  [8192, 40960, 131072, 8552448],
  [8192, 40960, 163840, 8519680],
  [8192, 40960, 8421376],
  [8192, 131072, 163840, 8429568],
  [8192, 172032, 8552448],
  [8192, 565256, 2261000, 8396834, 8421376, 11182114],
  [16384, 8404992],
  [20480, 86017, 8454145],
  [32768, 32776, 8388616],
  [32768, 40960, 8396800],
  [32768, 8421376],
  [131072, 8396800, 8429568, 8552448],
  [131072, 8519680],
  [163840, 172032, 8396800],
  [163848, 8552456],
  [172032, 8560640],
  [8388608],
  [8388616, 8429568, 8429576],
  [8396800, 8421376, 8429568],
  [8396800, 8552448, 8560640],
  [8192, 8226, 2261000, 8421376, 8953864, 11182114],
  [8192, 32768, 2261000, 8396834, 8953864, 11182114]
]

/-- Select a row, padding each certificate to six equations with zero rows. -/
def row (branch : Fin 26) (i : Fin 6) : ℕ :=
  (contradictorySubsystems[branch.val]!)[i.val]?.getD 0

@[expose] def bit (r j : ℕ) : ZMod 2 := if r.testBit j then 1 else 0

set_option maxHeartbeats 0 in
private theorem checks : ∀ branch : Fin 26,
    (∀ j : Fin 23, ∑ i : Fin 6, bit (row branch i) j = 0) ∧
    ∑ i : Fin 6, bit (row branch i) 23 ≠ 0 := by
  decide +kernel

/-- A binary correction system with zero column sums and an odd right-hand
side sum is inconsistent. -/
theorem no_correction_of_row_sums {n : ℕ} (r : Fin n → ℕ)
    (hc : ∀ j : Fin 23, ∑ i : Fin n, bit (r i) j = 0)
    (hr : ∑ i : Fin n, bit (r i) 23 ≠ 0) (digits : Fin 23 → ZMod 2) :
    ¬ ∀ i : Fin n, ∑ j : Fin 23, bit (r i) j * digits j = bit (r i) 23 := by
  intro h
  apply hr
  calc
    ∑ i : Fin n, bit (r i) 23 =
        ∑ i : Fin n, ∑ j : Fin 23, bit (r i) j * digits j :=
      Finset.sum_congr rfl (fun i _ => (h i).symm)
    _ = ∑ j : Fin 23, (∑ i : Fin n, bit (r i) j) * digits j := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = 0 := by simp [hc]

/-- Every listed subsystem of the actual mod-4 correction matrices is
inconsistent for all 23 correction digits, including every permitted
positive-degree coefficient in the (4,3,6) normal form. -/
theorem no_mod_four_correction (branch : Fin 26) (digits : Fin 23 → ZMod 2) :
    ¬ ∀ i : Fin 6, ∑ j : Fin 23, bit (row branch i) j * digits j = bit (row branch i) 23 :=
  no_correction_of_row_sums _ (checks branch).1 (checks branch).2 digits

/-- A full correction matrix is inconsistent as soon as it contains one of
the checked augmented-row subsystems. -/
theorem no_correction_of_contains (constraints : Set ℕ) (branch : Fin 26)
    (contains : ∀ i, row branch i ≠ 0 → row branch i ∈ constraints)
    (digits : Fin 23 → ZMod 2) :
    ¬ ∀ r ∈ constraints, ∑ j : Fin 23, bit r j * digits j = bit r 23 := by
  intro lifts
  apply no_mod_four_correction branch digits
  intro i
  by_cases hi : row branch i = 0
  · simp [hi, bit]
  · exact lifts _ (contains i hi)

end SmallCubic.TwoPoint.PrimaryTwo
