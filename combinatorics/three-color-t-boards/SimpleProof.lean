import EfficientCheck
import ColorSymmetry

/-!
A small certificate for more than sixty labeled three-color T boards.
The six boards share seven rows. They are records 841, 842, 843, 845, 846, 849
of the discovery data, copied in full so this proof imports no extended batches.
All finite checks reduce inside Lean’s kernel; discovery is not assumed correct.
-/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.Simple

/-- The first seven rows, shared by all six certificates. -/
def commonRows : Board := [
  [0],
  [0,0,0],
  [2,1,1,2,1],
  [2,1,0,2,2,2,1],
  [0,1,0,1,2,2,0,0,1],
  [2,2,1,1,1,2,1,2,2,2,2],
  [0,1,2,0,1,1,1,2,2,1,1,1,0]
]

def board0 : Board := commonRows ++ [
  [0,0,1,0,2,2,0,0,2,0,2,1,2,1,2],
  [1,0,1,1,0,0,2,2,0,0,0,2,1,0,0,0,1],
  [1,2,0,2,0,2,1,0,1,1,0,2,0,1,2,0,1,0,0]
]

def board1 : Board := commonRows ++ [
  [0,0,2,0,1,1,0,0,0,2,1,2,1,0,1],
  [1,0,2,0,2,2,0,2,1,0,0,0,2,0,0,1,2],
  [1,2,0,0,1,0,1,1,0,2,1,2,0,2,2,0,1,0,0]
]

def board2 : Board := commonRows ++ [
  [1,0,0,2,2,0,2,0,0,0,1,0,0,0,2],
  [2,1,2,0,2,0,2,0,1,0,1,1,0,2,1,0,1],
  [0,2,1,0,0,1,1,0,2,2,0,1,2,0,0,2,1,2,1]
]

def board3 : Board := commonRows ++ [
  [1,0,1,0,1,1,0,0,0,0,1,2,1,2,0],
  [2,0,2,0,0,2,1,0,2,2,0,0,2,2,0,1,0],
  [1,0,0,1,1,0,0,2,0,2,0,2,1,0,2,1,2,0,1]
]

def board4 : Board := commonRows ++ [
  [2,0,1,0,0,2,0,0,0,2,1,2,1,0,1],
  [1,0,1,1,0,2,0,2,1,0,0,0,2,0,2,2,0],
  [1,0,0,1,2,0,0,1,0,2,1,2,0,2,2,0,1,1,0]
]

def board5 : Board := commonRows ++ [
  [2,1,2,0,2,1,2,1,0,2,2,0,2,0,0],
  [0,0,0,2,1,0,0,0,1,0,0,2,0,1,1,0,1],
  [1,0,2,2,0,1,2,0,2,0,0,1,0,1,1,0,0,2,1]
]

def seeds : List Board := [board0, board1, board2, board3, board4, board5]

/-- A certificate for each representative’s 81 ordered T patterns. -/
theorem seeds_fast_valid : ∀ b ∈ seeds, FastValid b := by decide +kernel

/-- The reflected representatives are checked by the same small certificate. -/
theorem reflected_seeds_fast_valid :
    ∀ b ∈ seeds, FastValid (b.map List.reverse) := by decide +kernel

/-- Six color renamings and two orientations of each representative. -/
def family : List Board := seeds.flatMap orbit

theorem family_length : family.length = 72 := by decide +kernel

/-- Exact equality of board arrays is checked; no hash assumption is used. -/
theorem family_nodup : family.Nodup := by decide +kernel

theorem family_valid : ∀ b ∈ family, Valid b := by
  intro b hb
  obtain ⟨s, hs, hb⟩ := List.mem_flatMap.mp hb
  exact orbit_valid_of_valid_and_reverse
    (seeds_fast_valid s hs).valid (reflected_seeds_fast_valid s hs).valid b hb

/-- The six explicit certificates give 72 distinct valid labeled boards. -/
theorem at_least_72 :
    ∃ f : Fin 72 → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  exact injective_family_of_list family 72
    (by rw [family_length]; exact Nat.le_refl 72) family_nodup family_valid

/-- In particular, there are more than sixty such boards. -/
theorem more_than_60 : MoreThanSixty := by
  exact ⟨family, by rw [family_length]; decide, family_nodup, family_valid⟩

/-- Board A in the written proof satisfies the exact ordered-pattern rule. -/
theorem board0_valid : Valid board0 :=
  (seeds_fast_valid board0 (by simp [seeds])).valid

/-- Compare the explicit witness with all six recolorings and both orientations
of each of the five published representatives. -/
theorem board0_not_published : board0 ∉ TBoards.published := by decide +kernel

/-- The exact requested conclusion: more than sixty boards, with an explicit
valid board outside all five published symmetry families. -/
theorem problem_solved :
    MoreThanSixty ∧ Valid board0 ∧ board0 ∉ TBoards.published :=
  ⟨more_than_60, board0_valid, board0_not_published⟩

end TBoards.Simple

#print axioms TBoards.Simple.at_least_72
#print axioms TBoards.Simple.more_than_60
#print axioms TBoards.Simple.problem_solved
