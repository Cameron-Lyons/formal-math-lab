import Bank

namespace Snake

set_option maxHeartbeats 0 in
private theorem checkedRows : ∀ row ∈ bank,
    row.length = 191 ∧ isSnake (vertices row) = true ∧
    ∀ backwards : Bool, canExtend ((orientedPath row backwards).take 172) 21 = false := by
  checkBankRows

theorem bank_valid (row : List Nat) (mem : row ∈ bank) :
    row.length = 191 ∧ IsSnake (vertices row) := by
  obtain ⟨length, valid, _⟩ := checkedRows row mem
  exact ⟨length, isSnake_sound valid⟩

/-- From either end, keep the first 171 steps of a published record and
    replace the remaining 20. No choice of 21 new steps makes a 192-step snake. -/
theorem bank_no_192_kernel (row : List Nat) (mem : row ∈ bank) (backwards : Bool)
    (tail : List Vertex) (len : tail.length = 21) :
    ¬ IsSnake (((orientedPath row backwards).take 172) ++ tail) :=
  no_extension ((checkedRows row mem).2.2 backwards) tail len

end Snake
