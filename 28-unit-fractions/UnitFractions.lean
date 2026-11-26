import UnitFractions.Lower
import UnitFractions.Upper

namespace UnitFractions28

/-- Every red-blue coloring of 1 through N contains a solution with 28 summands
exactly when N ≥ 2352. This is Gaiser and Ramezanpour's Conjecture 1.3 at 28. -/
theorem forces_iff (N : Nat) : Forces N ↔ 2352 ≤ N := by
  constructor
  · intro forces
    have : ¬ N ≤ 2351 := fun h => lower (forces.mono h)
    omega
  · intro largeEnough
    exact upper.mono largeEnough

end UnitFractions28
