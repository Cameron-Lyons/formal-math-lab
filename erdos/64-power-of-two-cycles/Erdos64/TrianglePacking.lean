import Erdos64.EvenNeighborhood

/-! Lifting a cycle after contracting disjoint triangles. -/
namespace Erdos64.TrianglePacking

/-- The cycle visits distinct blocks in cyclic order, entering at `enter i`
and leaving at `leave i`. At distinct ports it can take either side of a
triangle. If a visit uses the same port twice, its successor takes the long
route. This produces a simple cycle of twice the quotient length. -/
theorem liftCycle {V : Type u} {G : Graph V} {r : Nat} (block : V → Fin r)
    (enter leave corner : Fin r → V)
    (enterBlock : ∀ i, block (enter i) = i) (leaveBlock : ∀ i, block (leave i) = i)
    (cornerBlock : ∀ i, block (corner i) = i)
    (crossing : ∀ i, G.adj (leave i) (enter (cycleNext i)))
    (triangle : ∀ i, enter i ≠ leave i →
      G.adj (enter i) (leave i) ∧ G.adj (enter i) (corner i) ∧ G.adj (corner i) (leave i))
    (isolated : ∀ i, enter i = leave i → enter (cycleNext i) ≠ leave (cycleNext i)) :
    HasCycle G (2*r) := by
  classical
  let long (i : Fin r) := ∃ j, cycleNext j = i ∧ enter j = leave j
  have longNext (i : Fin r) : long (cycleNext i) ↔ enter i = leave i := by
    refine ⟨?_, fun h => ⟨i, rfl, h⟩⟩
    rintro ⟨j, eq, same⟩
    exact Identification.nextInjective eq ▸ same
  have distinct {i : Fin r} (h : long i) : enter i ≠ leave i := by
    obtain ⟨j, rfl, same⟩ := h
    exact isolated j same

  -- A zero visit borrows the entering port of its successor as its second vertex.
  let first (i : Fin r) := if long i then corner i else enter i
  let second (i : Fin r) := if enter i = leave i then enter (cycleNext i) else leave i
  have firstBlock (i : Fin r) : block (first i) = i := by
    unfold first
    split <;> simp [cornerBlock, enterBlock]
  apply EvenNeighborhood.interleaveCycle first second
  · intro i j eq
    simpa only [firstBlock] using congrArg block eq
  · intro i j eq
    have blocks := congrArg block eq
    simp only [second] at eq blocks
    split at eq <;> split at eq <;>
      grind [Identification.nextInjective]
  · intro i j eq
    have blocks := congrArg block eq
    rw [firstBlock] at blocks
    by_cases same : enter j = leave j
    · have index : i = cycleNext j := by simpa [second, same, enterBlock] using blocks
      rw [index] at eq
      have edges := triangle (cycleNext j) (isolated j same)
      simp [first, second, (longNext j).2 same, same] at eq
      exact G.loopless _ (eq ▸ edges.2.1)
    · have index : i = j := by simpa [second, same, leaveBlock] using blocks
      rw [index] at eq
      have edges := triangle j same
      simp [first, second, same] at eq
      split at eq
      · exact G.loopless _ (eq ▸ edges.2.2)
      · exact same eq
  · intro i
    by_cases same : enter i = leave i
    · have short : ¬ long i := fun h => distinct h same
      simpa [first, second, short, same] using crossing i
    · have edges := triangle i same
      by_cases h : long i <;> simp [first, second, same, h, edges.1, edges.2.2]
  · intro i
    by_cases same : enter i = leave i
    · simpa [first, second, longNext, same] using (triangle _ (isolated i same)).2.1
    · simpa [first, second, longNext, same] using crossing i

end Erdos64.TrianglePacking
