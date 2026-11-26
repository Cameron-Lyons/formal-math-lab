import UnitFractions.Basic

namespace UnitFractions28

/-- Divide an integer sum by 4704. A summand of weight `w` gives
the unit fraction with denominator `4704 / w`. -/
private def row (s : Nat) (groups : List (Nat × Nat)) : Nat × List Nat :=
  (4704 / s, groups.flatMap fun (m, w) => List.replicate m (4704 / w))

private def identities : List (Nat × List Nat) :=
  [2, 3, 4, 6, 24, 42, 56, 84].map (fun w => row (28 * w) [(28, w)]) ++ [
    row 84 [(14, 2), (14, 4)],
    row 1568 [(13, 112), (1, 84), (14, 2)],
    row 1568 [(9, 168), (18, 3), (1, 2)],
    row 2352 [(1, 1568), (1, 672), (15, 6), (11, 2)],
    row 1568 [(1, 1176), (13, 24), (13, 6), (1, 2)],
    row 2352 [(1, 1568), (10, 42), (15, 24), (2, 2)]
  ]

private theorem identities_valid : ∀ r ∈ identities,
    let (target, xs) := r
    1 ≤ target ∧ target ≤ 2352 ∧ xs.length = 28 ∧ (∀ d ∈ xs, 1 ≤ d ∧ d ≤ 2352) ∧
    (xs.map reciprocal).sum = reciprocal target := by
  decide +kernel

private theorem monochromatic_row (c : Nat → Bool) :
    ∃ r ∈ identities,
      let (target, xs) := r
      ∀ d ∈ xs, c d = c target := by
  simp [identities, row, List.flatMap_cons]
  -- Split on the colors of weights 2 and 3 in the integer sums.
  cases h₂ : c (4704 / 2) <;> cases h₃ : c (4704 / 3) <;> grind

theorem upper : Forces 2352 := by
  intro color
  obtain ⟨⟨a, xs⟩, hrow, hcolor⟩ := monochromatic_row color
  obtain ⟨ha, hbound, hlen, hrange, heq⟩ := identities_valid _ hrow
  exact ⟨a, xs, ha, hbound, hlen, fun d hd =>
    ⟨(hrange d hd).1, (hrange d hd).2, hcolor d hd⟩, heq⟩

end UnitFractions28
