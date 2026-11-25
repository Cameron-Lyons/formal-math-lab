import Erdos64.PathFree
import Erdos64.DominatingCases
import Erdos64.NetAndTripod

namespace Erdos64

/-- Every nonempty simple graph of minimum degree at least three with no
induced P₁₄ ⊔ K₁ contains a simple cycle of length 4, 8, or 16. -/
theorem cycle_of_P14_plus_isolate_free {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (free : ¬ HasPathIso G 14) :
    HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 := by
  by_cases path : HasInducedPath G 14
  · exact cycle_of_dominatingP14 degree (dominatingOfNoPathIso path free)
  · exact cycle_of_P14_free degree path

/-- The Erdős–Gyárfás conclusion for this forbidden induced subgraph. -/
theorem power_of_two_cycle_of_P14_plus_isolate_free {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (free : ¬ HasPathIso G 14) :
    ∃ k : Nat, 2 ≤ k ∧ HasCycle G (2^k) := by
  rcases cycle_of_P14_plus_isolate_free degree free with four | eight | sixteen
  · exact ⟨2, by decide, four⟩
  · exact ⟨3, by decide, eight⟩
  · exact ⟨4, by decide, sixteen⟩

end Erdos64
