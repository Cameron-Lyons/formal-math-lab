module

public import TwoPointPrimaryTwo

public section

namespace SmallCubic.TwoPoint.AlternateTwo

open SmallCubic.TwoPoint.PrimaryTwo (bit no_correction_of_row_sums)

/-- Augmented binary rows as in the primary chart. Python verifies that one
of these 37 subsystems occurs in every terminal correction matrix. -/
def contradictorySubsystems : Array (List ℕ) := #[
  [8192, 32768, 524288, 2129920, 11018240],
  [8192, 32768, 8429568],
  [8192, 40960, 8421376],
  [8192, 131072, 163840, 8429568],
  [8192, 524288, 8421376, 10518528, 11018240],
  [8192, 8396800],
  [8192, 8429568, 8519680, 8552448],
  [16384, 1048576, 9453568],
  [16384, 1064960, 9437184],
  [16384, 8404992],
  [20480, 86017, 8454145],
  [32768, 40960, 8396800],
  [32768, 131072, 8552448],
  [32768, 163840, 8519680],
  [32768, 2097152, 10518528],
  [32768, 2629632, 11051008],
  [32768, 8421376],
  [40960, 524288, 8953856],
  [40960, 8429568],
  [65536, 8454144],
  [131072, 163840, 8421376],
  [131072, 524288, 9043968],
  [131072, 655360, 8912896],
  [131072, 8519680],
  [163840, 172032, 8396800],
  [172032, 8560640],
  [524288, 565248, 8429568],
  [524288, 8912896],
  [1048576, 1064960, 8404992],
  [2097152, 10485760],
  [2629632, 2662400, 8421376],
  [4194304, 12582912],
  [8388608],
  [8396800, 8421376, 8429568],
  [8396800, 8552448, 8560640],
  [8404992, 9437184, 9453568],
  [8421376, 8519680, 8552448]
]

def row (branch : Fin 37) (i : Fin 5) : ℕ :=
  (contradictorySubsystems[branch.val]!)[i.val]?.getD 0

set_option maxHeartbeats 0 in
private theorem checks : ∀ branch : Fin 37,
    (∀ j : Fin 23, ∑ i : Fin 5, bit (row branch i) j = 0) ∧
    ∑ i : Fin 5, bit (row branch i) 23 ≠ 0 := by
  decide +kernel

/-- Inconsistency applies to the second and third binary digit corrections. -/
theorem no_correction (branch : Fin 37) (digits : Fin 23 → ZMod 2) :
    ¬ ∀ i : Fin 5, ∑ j : Fin 23, bit (row branch i) j * digits j = bit (row branch i) 23 :=
  no_correction_of_row_sums _ (checks branch).1 (checks branch).2 digits

theorem no_correction_of_contains (constraints : Set ℕ) (branch : Fin 37)
    (contains : ∀ i, row branch i ≠ 0 → row branch i ∈ constraints)
    (digits : Fin 23 → ZMod 2) :
    ¬ ∀ r ∈ constraints, ∑ j : Fin 23, bit r j * digits j = bit r 23 := by
  intro lifts
  apply no_correction branch digits
  intro i
  by_cases hi : row branch i = 0
  · simp [hi, bit]
  · exact lifts _ (contains i hi)

end SmallCubic.TwoPoint.AlternateTwo
