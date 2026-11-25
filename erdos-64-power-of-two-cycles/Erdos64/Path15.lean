import Erdos64.LongPath

namespace Erdos64

set_option maxHeartbeats 0 in
private theorem path14Closes : closesPathWith longestAnchor 14 30 (pathRows 14) = true := by
  native_decide

/-- In a host with no C₄, C₈ or C₁₆, the presence of an induced P₁₄ forces
the presence of an induced P₁₅, possibly on different vertices. -/
theorem path15_of_path14 {V : Type u} {G : Graph V} (degree : MinDegreeThree G)
    (noCycles : ¬ (HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16))
    (shorter : HasInducedPath G 14) : HasInducedPath G 15 := by
  obtain ⟨board⟩ := pathBoardCopy shorter
  exact Classical.byContradiction fun h =>
    closesPathWith_sound degree noCycles h 30 _ board path14Closes

end Erdos64
