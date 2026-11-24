import KernelChecks

namespace Snake

/-- An explicit consequence of validating the published 191-step records. -/
theorem exists_191 : ∃ path : List Vertex, path.length = 192 ∧ IsSnake path := by
  obtain ⟨row, mem⟩ := List.exists_mem_of_length_pos (show 0 < bank.length by rw [bank_size]; decide)
  obtain ⟨hlen, hs⟩ := bank_valid row mem
  exact ⟨vertices row, by simp [vertices, hlen], hs⟩

/-- Distinct published rows are inequivalent, even after reversal. -/
theorem bank_pairwise_inequivalent : bank.Pairwise (fun p q => ¬ Equivalent p q) := by
  have checked : bank.Pairwise (fun p q => fresh p [q] = true) := by native_decide
  exact checked.imp (fun h => fresh_sound h _ (by simp))

/-- The first 156 steps of a bank row in its original or reversed orientation. -/
def bankPrefix (row : List Nat) (backwards : Bool) : List Vertex :=
  (orientedPath row backwards).take 157

private theorem bank_search : ∀ w ∈ bank, ∀ backwards : Bool,
    canExtend (bankPrefix w backwards) 36 = false := by native_decide

/-- After 156 steps in either orientation of a published record, every possible
    continuation of 36 more steps repeats a vertex or violates a distance condition. -/
theorem bank_no_192 (row : List Nat) (mem : row ∈ bank) (backwards : Bool)
    (tail : List Vertex) (len : tail.length = 36) :
    ¬ IsSnake (bankPrefix row backwards ++ tail) :=
  no_extension (bank_search row mem backwards) tail len

/-- Applying a Hamming-distance-preserving map to every vertex preserves the
    snake conditions. This covers a common permutation or flip of coordinates. -/
theorem IsSnake.map {vs : List Vertex} (hv : IsSnake vs) (f : Vertex → Vertex)
    (hf : ∀ x y, hamming (f x) (f y) = hamming x y) : IsSnake (vs.map f) := by
  match vs with
  | [] | [_] => trivial
  | x :: y :: ys =>
    obtain ⟨adjacent, separated, tail⟩ := hv
    refine ⟨(hf x y).trans adjacent, ?_, IsSnake.map (vs := y :: ys) tail f hf⟩
    simpa only [List.forall_mem_map, hf] using separated

/-- An arbitrary 192-step snake cannot have a first 156-step segment that an
    isometry sends to an oriented 156-step bank prefix. -/
theorem bank_no_192_up_to_isometry (row : List Nat) (mem : row ∈ bank) (backwards : Bool)
    (start tail : List Vertex) (len : tail.length = 36)
    (f : Vertex → Vertex) (hf : ∀ x y, hamming (f x) (f y) = hamming x y)
    (align : start.map f = bankPrefix row backwards) : ¬ IsSnake (start ++ tail) := by
  intro h
  have hs := h.map f hf
  rw [List.map_append, align] at hs
  exact bank_no_192 row mem backwards (tail.map f) (by simpa using len) hs

end Snake
