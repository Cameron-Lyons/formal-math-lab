import Bank

namespace Snake

/-- Distances to the initial vertex after each of the first seventeen steps
(including distance zero at the start). -/
def endProfile (p : List Vertex) : List Nat :=
  match p with
  | [] => []
  | x :: xs => 0 :: (xs.take 17).map (hamming x)

theorem endProfile_map (f : Vertex → Vertex)
    (hf : ∀ x y, hamming (f x) (f y) = hamming x y) (p : List Vertex) :
    endProfile (p.map f) = endProfile p := by
  cases p with
  | nil => rfl
  | cons x xs =>
    simp only [List.map_cons, endProfile, ← List.map_take, List.map_map]
    simp [Function.comp_def, hf]

/-- Every published row has a different distance profile when read backwards. -/
theorem bank_end_profiles_differ (w : List Nat) (hw : w ∈ bank) :
    endProfile (vertices w) ≠ endProfile (vertices w).reverse := by
  revert w
  checkBankRows

end Snake
