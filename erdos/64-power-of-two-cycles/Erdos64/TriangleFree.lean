import Erdos64.TriangleFreeSearch

namespace Erdos64

private theorem pathCases : ∀ i : Fin 16,
    closesTriangleFree (i.val+1) false 70 (pathRows (i.val+1)) = true := by
  native_decide

private theorem dominatingCase : closesTriangleFree 17 true 30 (pathRows 17) = true := by
  native_decide

private theorem singletonPath {V : Type u} [Nonempty V] (G : Graph V) :
    HasInducedPath G 1 := by
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨⟨fun _ => v, ?_, ?_⟩⟩
  · intro i j hi hj _
    omega
  · intro i j hi hj
    have : i = 0 := by omega
    have : j = 0 := by omega
    subst i j
    simp [G.loopless, pathAdj]

/-- Without a cycle of length 4, 8, or 16, a triangle-free graph of minimum
degree three has an induced path on seventeen vertices. -/
private theorem path17 {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (tri : ¬ HasCycle G 3)
    (none : ¬ (HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16)) : HasInducedPath G 17 := by
  have grow (i : Nat) (bound : i ≤ 16) : HasInducedPath G (i+1) := by
    induction i with
    | zero => exact singletonPath G
    | succ i ih =>
      apply Classical.byContradiction
      intro noLong
      obtain ⟨c⟩ := pathBoardCopy (ih (by omega))
      exact closesTriangleFree_sound degree tri none (fun _ => noLong) 70 _ (by simp) c
        (by simp) (pathCases ⟨i, by omega⟩)
  exact grow 16 (by decide)

/-- The Erdős–Gyárfás conclusion for triangle-free, P₁₇-free graphs. -/
theorem cycle_of_triangleFree_P17_free {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (tri : ¬ HasCycle G 3) (free : ¬ HasInducedPath G 17) :
    HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 := by
  exact Classical.byContradiction fun none => free (path17 degree tri none)

/-- A triangle-free simple graph of minimum degree three with a dominating
induced P₁₇ contains a simple cycle of length 4, 8, or 16. -/
theorem cycle_of_triangleFree_dominatingP17 {V : Type u} {G : Graph V}
    (degree : MinDegreeThree G) (tri : ¬ HasCycle G 3)
    (path : HasDominatingInducedPath G 17) : HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 := by
  apply Classical.byContradiction
  intro none
  obtain ⟨c, dom⟩ := path
  let board : Copy G (pathRows 17).size (adjAt (pathRows 17)) := {
    lab := c.lab
    inj := c.inj
    edge := fun {i j} hi hj => by
      rw [pathRows_adj (r := 17) hi hj]
      exact c.edge hi hj }
  exact closesTriangleFree_sound degree tri none (by simp) 30 _ (by simp) board
    (fun _ => dom) dominatingCase

/-- Every nonempty triangle-free simple graph of minimum degree at least three
with no induced P₁₇ ⊔ K₁ contains a simple cycle of length 4, 8, or 16. -/
theorem cycle_of_triangleFree_P17_plus_isolate_free {V : Type u} [Nonempty V] {G : Graph V}
    (degree : MinDegreeThree G) (tri : ¬ HasCycle G 3) (free : ¬ HasPathIso G 17) :
    HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16 := by
  by_cases path : HasInducedPath G 17
  · exact cycle_of_triangleFree_dominatingP17 degree tri (dominatingOfNoPathIso path free)
  · exact cycle_of_triangleFree_P17_free degree tri path

end Erdos64
