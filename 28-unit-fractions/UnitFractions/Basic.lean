import Std

namespace UnitFractions28

/-- The unit fraction 1/n. -/
def reciprocal (n : Nat) : Rat := 1 / (n : Rat)

/-- Every red-blue coloring of 1 through N has a solution. The list holds the
28 denominators on the left of the equation, including any repetitions. -/
def Forces (N : Nat) : Prop :=
  ∀ color : Nat → Bool, ∃ (target : Nat) (xs : List Nat),
    1 ≤ target ∧ target ≤ N ∧ xs.length = 28 ∧
    (∀ x ∈ xs, 1 ≤ x ∧ x ≤ N ∧ color x = color target) ∧
    (xs.map reciprocal).sum = reciprocal target

/-- A solution on a smaller interval also works on a larger one. -/
theorem Forces.mono {m n : Nat} (forces : Forces m) (le : m ≤ n) : Forces n := by
  intro color
  obtain ⟨target, xs, pos, bound, length, terms, sum⟩ := forces color
  refine ⟨target, xs, pos, Nat.le_trans bound le, length, ?_, sum⟩
  intro x hx
  obtain ⟨xpos, xbound, sameColor⟩ := terms x hx
  exact ⟨xpos, Nat.le_trans xbound le, sameColor⟩

end UnitFractions28
