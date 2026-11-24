import Simple.Order12.Test

/-! The 49 patterns: `k` squares, of which `j` are fixed by squaring. -/

-- The SAT goals exceed the default limits. They run one at a time to save memory.
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace E1486.Order12

private theorem squares0 (j : Nat) (hj : j ≤ 0) (hp : (0-j)%2 = 0) (g : Graph) :
    check 0 j g = false := by
  obtain rfl : j = 0 := by omega
  all_goals refute_pattern

private theorem squares1 (j : Nat) (hj : j ≤ 1) (hp : (1-j)%2 = 0) (g : Graph) :
    check 1 j g = false := by
  obtain rfl : j = 1 := by omega
  all_goals refute_pattern

private theorem squares2 (j : Nat) (hj : j ≤ 2) (hp : (2-j)%2 = 0) (g : Graph) :
    check 2 j g = false := by
  obtain rfl | rfl : j = 0 ∨ j = 2 := by omega
  all_goals refute_pattern

private theorem squares3 (j : Nat) (hj : j ≤ 3) (hp : (3-j)%2 = 0) (g : Graph) :
    check 3 j g = false := by
  obtain rfl | rfl : j = 1 ∨ j = 3 := by omega
  all_goals refute_pattern

private theorem squares4 (j : Nat) (hj : j ≤ 4) (hp : (4-j)%2 = 0) (g : Graph) :
    check 4 j g = false := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 2 ∨ j = 4 := by omega
  all_goals refute_pattern

private theorem squares5 (j : Nat) (hj : j ≤ 5) (hp : (5-j)%2 = 0) (g : Graph) :
    check 5 j g = false := by
  obtain rfl | rfl | rfl : j = 1 ∨ j = 3 ∨ j = 5 := by omega
  all_goals refute_pattern

private theorem squares6 (j : Nat) (hj : j ≤ 6) (hp : (6-j)%2 = 0) (g : Graph) :
    check 6 j g = false := by
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 := by omega
  all_goals refute_pattern

private theorem squares7 (j : Nat) (hj : j ≤ 7) (hp : (7-j)%2 = 0) (g : Graph) :
    check 7 j g = false := by
  obtain rfl | rfl | rfl | rfl : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 := by omega
  all_goals refute_pattern

private theorem squares8 (j : Nat) (hj : j ≤ 8) (hp : (8-j)%2 = 0) (g : Graph) :
    check 8 j g = false := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 := by omega
  all_goals refute_pattern

private theorem squares9 (j : Nat) (hj : j ≤ 9) (hp : (9-j)%2 = 0) (g : Graph) :
    check 9 j g = false := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 9 := by omega
  all_goals refute_pattern

private theorem squares10 (j : Nat) (hj : j ≤ 10) (hp : (10-j)%2 = 0) (g : Graph) :
    check 10 j g = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
      j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 := by omega
  all_goals refute_pattern

private theorem squares11 (j : Nat) (hj : j ≤ 11) (hp : (11-j)%2 = 0) (g : Graph) :
    check 11 j g = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
      j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 9 ∨ j = 11 := by omega
  all_goals refute_pattern

private theorem squares12 (j : Nat) (hj : j ≤ 12) (hp : (12-j)%2 = 0) (g : Graph) :
    check 12 j g = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 ∨ j = 12 := by omega
  all_goals refute_pattern

/-- Every pattern fails the test. -/
theorem refute (k j : Nat) (hk : k ≤ 12) (hj : j ≤ k) (hp : (k-j)%2 = 0) (g : Graph) :
    check k j g = false := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
      k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
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

end E1486.Order12
