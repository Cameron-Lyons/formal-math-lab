import UnitFractions.Basic

namespace UnitFractions

/-- In a row for `1/a`, each pair `(m, d)` contributes `m` copies of `1/d`. -/
private def row (a : Nat) (groups : List (Nat × Nat)) : Nat × List Nat :=
  (a, groups.flatMap fun (m, d) => List.replicate m d)

private def identities : List (Nat × List Nat) :=
  -- For each d, 26 copies of 1/(26d) add up to 1/d.
  [2, 3, 4, 8, 13, 52, 78].map (fun d => row d [(26, 26 * d)]) ++ [
    -- The six remaining rows appear in the same order as in the walkthrough.
    row 2 [(13, 39), (13, 78)],
    row 3 [(12, 39), (1, 52), (13, 2028)],
    row 2 [(1, 3), (2, 13), (6, 1352), (17, 2028)],
    row 2 [(1, 3), (16, 104), (3, 338), (4, 1352), (2, 2028)],
    row 2 [(1, 3), (1, 8), (12, 338), (1, 1352), (11, 2028)],
    row 3 [(1, 4), (16, 208), (8, 1352), (1, 2028)]
  ]

private theorem identities_valid : ∀ r ∈ identities,
    let (target, xs) := r
    1 ≤ target ∧ target ≤ 2028 ∧ xs.length = 26 ∧ (∀ d ∈ xs, 1 ≤ d ∧ d ≤ 2028) ∧
    (xs.map reciprocal).sum = reciprocal target := by
  decide +kernel

private theorem monochromatic_row (c : Nat → Bool) :
    ∃ r ∈ identities,
      let (target, xs) := r
      ∀ d ∈ xs, c d = c target := by
  -- Expand each row into the color equalities that make it monochromatic.
  simp [identities, row, List.flatMap_cons]
  -- If every row is avoided, d and 26d have opposite colors. The first two
  -- mixed rows then force 2 and 3 to agree. The next three force 13, 104
  -- and 8 to the opposite color, making the last row monochromatic.
  cases h₂ : c 2 <;> cases h₃ : c 3 <;> grind

theorem upper : Forces 2028 := by
  intro color
  obtain ⟨⟨a, xs⟩, hrow, hcolor⟩ := monochromatic_row color
  obtain ⟨ha, hbound, hlen, hrange, heq⟩ := identities_valid _ hrow
  exact ⟨a, xs, ha, hbound, hlen, fun d hd =>
    ⟨(hrange d hd).1, (hrange d hd).2, hcolor d hd⟩, heq⟩

end UnitFractions
