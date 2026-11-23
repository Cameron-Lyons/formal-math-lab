import Ramsey556.SquarePaths

namespace Ramsey556

-- The two samples in a block cannot both receive color 0. Once one nonzero
-- sample per block is selected, a bridge of color 1 (respectively 2) means
-- that color can appear in only one column (row). The other column (row)
-- would have both its samples in color 2 (1), which is also forbidden.
private theorem conflictingBlocks :
    ∀ (bridge a b c d : Fin 3),
      bridge ≠ 0 → a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
      let colors := #v[a, b, c, d]
      ∃ x y : Fin 4, colors[x] = colors[y] ∧
        ∀ i j : Fin 2, SquareConflict bridge colors[x] x y i j := by
  dsimp only
  decide

private theorem noSampleAssignment (bridge : Fin 3) (hbridge : bridge ≠ 0)
    (spoke : Fin 4 → Fin 2 → Fin 3)
    (avoid : ∀ k a b s t, SquareConflict bridge k a b s t →
      spoke a s = k → spoke b t ≠ k) : False := by
  let pick (b : Fin 4) : Fin 2 := if spoke b 0 = 0 then 1 else 0
  have nonzero (b : Fin 4) : spoke b (pick b) ≠ 0 := by
    by_cases h : spoke b 0 = 0
    · simpa [pick, h] using avoid 0 b b 0 1 (Or.inl ⟨rfl, rfl, by decide⟩) h
    · simp [pick, h]
  let color (b : Fin 4) := spoke b (pick b)
  let colors := #v[color 0, color 1, color 2, color 3]
  have entry (i : Fin 4) : colors[i] = color i := by
    obtain ⟨n, hn⟩ := i
    have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨a, b, same, conflict⟩ :=
    conflictingBlocks bridge _ _ _ _ hbridge (nonzero 0) (nonzero 1) (nonzero 2) (nonzero 3)
  change colors[a] = colors[b] at same
  change ∀ i j, SquareConflict bridge colors[a] a b i j at conflict
  rw [entry a, entry b] at same
  rw [entry a] at conflict
  exact avoid (color a) a b (pick a) (pick b) (conflict _ _) rfl same.symm

/-- No choice of colors for the 32 edges to a new vertex can avoid all
seven-edge paths in the square when its specified bridge has color 1 or 2. -/
theorem squareFrame_no_compatible (c : Coloring 32) (hc : SquareFrame c)
    (hb : squareBridge c ≠ 0) (f : Fin 32 → Fin 3) : ¬ Compatible c f := by
  intro compat
  apply noSampleAssignment (squareBridge c) hb (fun b s => f (squareSample b s))
  intro k a b s t h
  exact compat _ _ _ (squareFrame_conflict c hc k a b s t h)

/-- Every extension of the square frame to 33 vertices has a monochromatic
9-cycle. At most five slots per block need the prescribed cross-block colors. -/
theorem hasMonoC9_of_squareFrame (c : Coloring 33) (hc : SquareFrame (dropLast c))
    (hb : squareBridge (dropLast c) ≠ 0) : HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  exact squareFrame_no_compatible (dropLast c) hc hb _ ((free_iff_compatible c).1 free).2

end Ramsey556
