import Simple.Leader

/-! The 64 patterns: `k` squares, of which `j` are fixed by squaring. -/

-- The SAT goals exceed the default limits. They run one at a time to save memory.
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace E1486.Order14
open E1486.Test

private theorem squares0 (j : Nat) (hj : j ≤ 0) (hp : (0-j)%2 = 0) (g : BitVec 196) :
    (check 14 0 j g && leads 14 0 j g) = false := by
  obtain rfl : j = 0 := by omega
  all_goals refute_leading

private theorem squares1 (j : Nat) (hj : j ≤ 1) (hp : (1-j)%2 = 0) (g : BitVec 196) :
    (check 14 1 j g && leads 14 1 j g) = false := by
  obtain rfl : j = 1 := by omega
  all_goals refute_leading

private theorem squares2 (j : Nat) (hj : j ≤ 2) (hp : (2-j)%2 = 0) (g : BitVec 196) :
    (check 14 2 j g && leads 14 2 j g) = false := by
  obtain rfl | rfl : j = 0 ∨ j = 2 := by omega
  all_goals refute_leading

private theorem squares3 (j : Nat) (hj : j ≤ 3) (hp : (3-j)%2 = 0) (g : BitVec 196) :
    (check 14 3 j g && leads 14 3 j g) = false := by
  obtain rfl | rfl : j = 1 ∨ j = 3 := by omega
  all_goals refute_leading

private theorem squares4 (j : Nat) (hj : j ≤ 4) (hp : (4-j)%2 = 0) (g : BitVec 196) :
    (check 14 4 j g && leads 14 4 j g) = false := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 2 ∨ j = 4 := by omega
  all_goals refute_leading

private theorem squares5 (j : Nat) (hj : j ≤ 5) (hp : (5-j)%2 = 0) (g : BitVec 196) :
    (check 14 5 j g && leads 14 5 j g) = false := by
  obtain rfl | rfl | rfl : j = 1 ∨ j = 3 ∨ j = 5 := by omega
  all_goals refute_leading

private theorem squares6 (j : Nat) (hj : j ≤ 6) (hp : (6-j)%2 = 0) (g : BitVec 196) :
    (check 14 6 j g && leads 14 6 j g) = false := by
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 := by omega
  all_goals refute_leading

private theorem squares7 (j : Nat) (hj : j ≤ 7) (hp : (7-j)%2 = 0) (g : BitVec 196) :
    (check 14 7 j g && leads 14 7 j g) = false := by
  obtain rfl | rfl | rfl | rfl : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 := by omega
  all_goals refute_leading

private theorem squares8 (j : Nat) (hj : j ≤ 8) (hp : (8-j)%2 = 0) (g : BitVec 196) :
    (check 14 8 j g && leads 14 8 j g) = false := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 := by omega
  all_goals refute_leading

private theorem squares9 (j : Nat) (hj : j ≤ 9) (hp : (9-j)%2 = 0) (g : BitVec 196) :
    (check 14 9 j g && leads 14 9 j g) = false := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 9 := by omega
  all_goals refute_leading

private theorem squares10 (j : Nat) (hj : j ≤ 10) (hp : (10-j)%2 = 0) (g : BitVec 196) :
    (check 14 10 j g && leads 14 10 j g) = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
      j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 := by omega
  all_goals refute_leading

private theorem squares11 (j : Nat) (hj : j ≤ 11) (hp : (11-j)%2 = 0) (g : BitVec 196) :
    (check 14 11 j g && leads 14 11 j g) = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
      j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 9 ∨ j = 11 := by omega
  all_goals refute_leading

private theorem squares12 (j : Nat) (hj : j ≤ 12) (hp : (12-j)%2 = 0) (g : BitVec 196) :
    (check 14 12 j g && leads 14 12 j g) = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 ∨ j = 12 := by omega
  all_goals refute_leading

private theorem squares13 (j : Nat) (hj : j ≤ 13) (hp : (13-j)%2 = 0) (g : BitVec 196) :
    (check 14 13 j g && leads 14 13 j g) = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 9 ∨ j = 11 ∨ j = 13 := by omega
  all_goals refute_leading

private theorem squares14 (j : Nat) (hj : j ≤ 14) (hp : (14-j)%2 = 0) (g : BitVec 196) :
    (check 14 14 j g && leads 14 14 j g) = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 ∨ j = 12 ∨ j = 14 := by omega
  all_goals refute_leading

/-- Every pattern fails the test or its ordering conditions. -/
theorem refute (k j : Nat) (hk : k ≤ 14) (hj : j ≤ k) (hp : (k-j)%2 = 0) (g : BitVec 196) :
    (check 14 k j g && leads 14 k j g) = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 := by omega
  · exact squares0 j hj hp g
  · exact squares1 j hj hp g
  · exact squares2 j hj hp g
  · exact squares3 j hj hp g
  · exact squares4 j hj hp g
  · exact squares5 j hj hp g
  · exact squares6 j hj hp g
  · exact squares7 j hj hp g
  · exact squares8 j hj hp g
  · exact squares9 j hj hp g
  · exact squares10 j hj hp g
  · exact squares11 j hj hp g
  · exact squares12 j hj hp g
  · exact squares13 j hj hp g
  · exact squares14 j hj hp g

end E1486.Order14
