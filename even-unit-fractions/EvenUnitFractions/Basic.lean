import Std

namespace EvenUnitFractions

/-- The unit fraction 1 / n. -/
def reciprocal (n : Nat) : Rat := 1 / (n : Rat)

/-- Every red-blue coloring of 1 through N has a monochromatic solution to
`1/x₁ + ... + 1/xₖ = 1/target`, with repetitions allowed. -/
def Forces (k N : Nat) : Prop :=
  ∀ color : Nat → Bool, ∃ (target : Nat) (xs : List Nat),
    1 ≤ target ∧ target ≤ N ∧ xs.length = k ∧
    (∀ x ∈ xs, 1 ≤ x ∧ x ≤ N ∧ color x = color target) ∧
    (xs.map reciprocal).sum = reciprocal target

/-- A solution on a smaller interval also works on a larger one. -/
theorem Forces.mono {k m n : Nat} (forces : Forces k m) (le : m ≤ n) : Forces k n := by
  intro color
  obtain ⟨target, xs, pos, bound, length, terms, sum⟩ := forces color
  refine ⟨target, xs, pos, Nat.le_trans bound le, length, ?_, sum⟩
  intro x hx
  obtain ⟨xpos, xbound, sameColor⟩ := terms x hx
  exact ⟨xpos, Nat.le_trans xbound le, sameColor⟩

/-- Sum of `m` copies of `1 / d`. -/
theorem sum_replicate_reciprocal (m d : Nat) :
    ((List.replicate m d).map reciprocal).sum = (m : Rat) * reciprocal d := by
  induction m with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.map_cons, List.sum_cons, ih, Rat.natCast_add,
      Rat.natCast_ofNat]
    grind

/-- Expand weighted groups `[(m₁, d₁), ...]` into a flat denominator list. -/
def expand (groups : List (Nat × Nat)) : List Nat :=
  groups.flatMap fun (m, d) => List.replicate m d

theorem length_expand (groups : List (Nat × Nat)) :
    (expand groups).length = (groups.map Prod.fst).sum := by
  induction groups with
  | nil => simp [expand]
  | cons p ps ih =>
    rcases p with ⟨m, d⟩
    simp [expand, List.flatMap_cons, List.length_append, List.length_replicate]

theorem mem_expand {groups : List (Nat × Nat)} {x : Nat} (hx : x ∈ expand groups) :
    ∃ p ∈ groups, 0 < p.1 ∧ x = p.2 := by
  induction groups with
  | nil => simp [expand] at hx
  | cons p ps ih =>
    rcases p with ⟨m, d⟩
    rw [expand, List.flatMap_cons, List.mem_append, List.mem_replicate] at hx
    rcases hx with ⟨hm, rfl⟩ | htail
    · exact ⟨(m, x), .head ps, Nat.pos_of_ne_zero hm, rfl⟩
    · obtain ⟨q, hq, hpos, rfl⟩ := ih htail
      exact ⟨q, .tail _ hq, hpos, rfl⟩

theorem sum_expand (groups : List (Nat × Nat)) :
    ((expand groups).map reciprocal).sum =
      (groups.map fun (m, d) => (m : Rat) * reciprocal d).sum := by
  induction groups with
  | nil => simp [expand]
  | cons p ps ih =>
    rcases p with ⟨m, d⟩
    rw [expand, List.flatMap_cons, List.map_append, List.sum_append,
      sum_replicate_reciprocal, List.map_cons, List.sum_cons]
    exact congrArg (((m : Rat) * reciprocal d) + ·) ih

end EvenUnitFractions
