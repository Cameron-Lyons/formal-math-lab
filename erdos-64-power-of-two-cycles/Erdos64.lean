import Erdos64.PathFree
import Erdos64.Path15
import Erdos64.TriangleFree
import Erdos64.Pathwidth
import Erdos64.TreewidthProfiles
import Erdos64.TetrahedronCover
import Erdos64.CutVertex
import Erdos64.EvenNeighborhood
import Erdos64.TrianglePacking
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

private theorem powerOfTwo {V : Type u} {G : Graph V}
    (h : HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16) :
    ∃ k : Nat, 2 ≤ k ∧ HasCycle G (2^k) := by
  rcases h with four | eight | sixteen
  · exact ⟨2, by decide, four⟩
  · exact ⟨3, by decide, eight⟩
  · exact ⟨4, by decide, sixteen⟩

/-- The Erdős–Gyárfás conclusion for this forbidden induced subgraph. -/
theorem power_of_two_cycle_of_P14_plus_isolate_free {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (free : ¬ HasPathIso G 14) :
    ∃ k : Nat, 2 ≤ k ∧ HasCycle G (2^k) :=
  powerOfTwo (cycle_of_P14_plus_isolate_free degree free)

/-- The conjecture for graphs with no induced path on fifteen vertices. -/
theorem cycle_of_P15_free {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (free : ¬ HasInducedPath G 15) :
    HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 := by
  apply Classical.byContradiction
  intro noCycles
  have shorter : HasInducedPath G 14 := Classical.byContradiction fun h =>
    noCycles (cycle_of_P14_free degree h)
  exact free (path15_of_path14 degree noCycles shorter)

/-- Every nonempty simple graph of minimum degree at least three with no
induced P₁₅ ⊔ K₁ contains a simple cycle of length 4, 8, or 16. -/
theorem cycle_of_P15_plus_isolate_free {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (free : ¬ HasPathIso G 15) :
    HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 := by
  by_cases path : HasInducedPath G 15
  · exact cycle_of_dominatingP15 degree (dominatingOfNoPathIso path free)
  · exact cycle_of_P15_free degree path

theorem power_of_two_cycle_of_P15_plus_isolate_free {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (free : ¬ HasPathIso G 15) :
    ∃ k : Nat, 2 ≤ k ∧ HasCycle G (2^k) :=
  powerOfTwo (cycle_of_P15_plus_isolate_free degree free)

end Erdos64
