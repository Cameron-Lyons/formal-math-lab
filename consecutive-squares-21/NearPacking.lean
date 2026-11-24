import Squares

/-! A near packing for the remaining rectangle, recorded as a search seed.
All 42 squares lie inside the board. Exactly 23 unit cells are empty and
23 are covered twice. -/

namespace Squares42.NearPacking

def placement : Placement := fun i =>
  (#v[(15, 16), (15, 17), (16, 29), (47, 49),
      (36, 68), (44, 48), (50, 37), (54, 37),
      (39, 49), (39, 54), (58, 38), (58, 44),
      (63, 79), (70, 79), (38, 30), (44, 51),
      (35, 21), (49, 41), (15, 19), (25, 19),
      (38, 38), (52, 50), (39, 59), (51, 61),
      (50, 73), (64, 38), (63, 51), (63, 65),
      (0, 16), (35, 71), (0, 0), (44, 21),
      (0, 69), (60, 21), (0, 31), (17, 68),
      (16, 0), (20, 49), (0, 49), (18, 29),
      (35, 0), (56, 0)] : Vector Cell 42)[i]

theorem in_bounds : ∀ i, (placement i).1 + side i ≤ 77 ∧
    (placement i).2 + side i ≤ 86 := by decide

/-- How many tiles cover the cell with this lower-left corner. -/
def occupancy (c : Cell) : Nat :=
  (List.finRange 42).countP fun i =>
    decide ((placement i).1 ≤ c.1 ∧ c.1 < (placement i).1 + side i ∧
      (placement i).2 ≤ c.2 ∧ c.2 < (placement i).2 + side i)

theorem occupancy_eq (c : Cell) :
    occupancy c = (List.finRange 42).countP (fun i => decide (c ∈ piece placement i)) := by
  obtain ⟨x,y⟩ := c
  simp only [occupancy, piece, mem_cells]

theorem coverage_counts :
    let hits := (cells (0,0) 77 86).map occupancy
    hits.count 0 = 23 ∧ hits.count 1 = 6576 ∧ hits.count 2 = 23 := by
  native_decide

end Squares42.NearPacking
