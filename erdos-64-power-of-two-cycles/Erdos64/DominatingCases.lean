import Erdos64.PathFreeSearch

/-! Power-of-two cycles forced by a dominating induced path. -/
namespace Erdos64

private theorem seed13Closes : closes 13 30 (pathRows 13) = true := by native_decide
private theorem seed14Closes : closes 14 30 (pathRows 14) = true := by native_decide

private theorem cycleOfDominatingSeed {V : Type u} {G : Graph V} {k : Nat}
    (degree : MinDegreeThree G) (path : HasDominatingInducedPath G k)
    (checked : closes k 30 (pathRows k) = true) :
    HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 := by
  apply Classical.byContradiction
  intro noCycles
  obtain ⟨c,dom⟩ := path
  let board : Copy G (pathRows k).size (adjAt (pathRows k)) := {
    lab := c.lab
    inj := fun hi hj eq => c.inj (by simpa only [pathRows_size] using hi)
      (by simpa only [pathRows_size] using hj) eq
    edge := by
      intro i j hi hj
      have hi' : i < k := by simpa only [pathRows_size] using hi
      have hj' : j < k := by simpa only [pathRows_size] using hj
      rw [pathRows_adj hi' hj']
      exact c.edge hi' hj' }
  exact closes_sound degree noCycles k 30 (pathRows k) (by simp) board dom checked

theorem cycle_of_dominatingP13 {V : Type u} {G : Graph V}
    (degree : MinDegreeThree G) (path : HasDominatingInducedPath G 13) :
    HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 :=
  cycleOfDominatingSeed degree path seed13Closes

theorem cycle_of_dominatingP14 {V : Type u} {G : Graph V}
    (degree : MinDegreeThree G) (path : HasDominatingInducedPath G 14) :
    HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 :=
  cycleOfDominatingSeed degree path seed14Closes

end Erdos64
