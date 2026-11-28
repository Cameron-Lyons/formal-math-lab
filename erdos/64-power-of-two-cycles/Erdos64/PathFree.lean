import Erdos64.PathFreeSearch

namespace Erdos64

/-- The twelve possible longest-path orders, from 2 through 13. -/
private theorem pathCases : ∀ i : Fin 12,
    closesPath (i.val + 2) 70 (pathRows (i.val + 2)) = true := by native_decide

private theorem hasEdgePath {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) : HasInducedPath G 2 := by
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨y, _, _, xy, _⟩ := degree x
  have ne : x ≠ y := fun h => G.loopless y (h ▸ xy)
  let f (i : Nat) := if i = 0 then x else y
  refine ⟨⟨f, ?_, ?_⟩⟩
  · intro i j hi hj eq
    by_cases ei : i = 0 <;> by_cases ej : j = 0 <;> simp [f,ei,ej] at eq <;> grind
  · intro i j hi hj
    by_cases ei : i = 0 <;> by_cases ej : j = 0 <;>
      simp [f,ei,ej,pathAdj,hi,hj,G.loopless,G.symm xy,xy] <;> omega

/-- Every nonempty simple graph of minimum degree at least three that has no
induced path on fourteen vertices contains a simple cycle of length 4, 8 or 16. -/
theorem cycle_of_P14_free {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (free : ¬ HasInducedPath G 14) :
    HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 := by
  apply Classical.byContradiction
  intro noCycles
  have along (j : Nat) (hj : j ≤ 12) : HasInducedPath G (j+2) := by
    induction j with
    | zero => exact hasEdgePath degree
    | succ j ih =>
      apply Classical.byContradiction
      intro noLong
      obtain ⟨p⟩ := pathBoardCopy (ih (by omega))
      exact closesPath_sound degree noCycles noLong 70 _ p (pathCases ⟨j, by omega⟩)
  exact free (along 12 (by decide))

end Erdos64
