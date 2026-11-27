import EvenUnitFractions.Lower

namespace UnitFractions33

open EvenUnitFractions

/-- A pair `(m, d)` in a row stands for `m` copies of `1/d`. -/
private def row (target : Nat) (groups : List (Nat × Nat)) : Nat × List Nat :=
  (target, expand groups)

private def identities : List (Nat × List Nat) :=
  [1, 3, 4, 9, 33, 36, 99].map (fun d => row d [(33, 33 * d)]) ++ [
    row 27 [(1, 99), (32, 1188)],
    row 1 [(9, 27), (24, 36)],
    row 3 [(2, 27), (1, 33), (8, 36), (22, 3267)],
    row 3 [(6, 27), (3, 33), (24, 1188)],
    row 2 [(3, 33), (6, 36), (24, 99)],
    row 2 [(1, 3), (21, 132), (6, 1089), (1, 1188), (4, 3267)],
    row 4 [(2, 9), (22, 1089), (9, 1188)],
    row 1 [(2, 3), (1, 4), (23, 297), (7, 1188)]
  ]

private theorem identities_valid : ∀ r ∈ identities,
    1 ≤ r.1 ∧ r.1 ≤ 3267 ∧ r.2.length = 33 ∧ (∀ d ∈ r.2, 1 ≤ d ∧ d ≤ 3267) ∧
    (r.2.map reciprocal).sum = reciprocal r.1 := by
  decide +kernel

private theorem monochromatic_row (c : Nat → Bool) :
    ∃ r ∈ identities, ∀ d ∈ r.2, c d = c r.1 := by
  simp [identities, row, expand, List.flatMap_cons]
  -- Each mixed row contains either 36 or 1188 = 33 * 36.
  cases h₃₆ : c 36 <;> cases h₃ : c 3 <;> grind

theorem upper : Forces 33 3267 := by
  intro c
  obtain ⟨⟨y, xs⟩, hrow, hcolor⟩ := monochromatic_row c
  obtain ⟨hy, hyN, hlen, hrange, heq⟩ := identities_valid _ hrow
  exact ⟨y, xs, hy, hyN, hlen, fun d hd =>
    ⟨(hrange d hd).1, (hrange d hd).2, hcolor d hd⟩, heq⟩

/-- The two-color 33-term reciprocal Rado number is exactly 3267. -/
theorem forces_iff (N : Nat) : Forces 33 N ↔ 3267 ≤ N := by
  constructor
  · intro h
    have hsmall : ¬ Forces 33 3266 := lower (k := 33) (by decide)
    have hlarge : ¬ N ≤ 3266 := fun le => hsmall (h.mono le)
    omega
  · exact upper.mono

end UnitFractions33
