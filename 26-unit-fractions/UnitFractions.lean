import UnitFractions.Lower
import UnitFractions.Upper

namespace UnitFractions

/-- Every red-blue coloring of 1 through N contains a solution with 26 summands
exactly when N ≥ 2028. This is Gaiser and Ramezanpour's Conjecture 1.3 at 26. -/
theorem forces_iff (N : Nat) : Forces N ↔ 2028 ≤ N := by
  constructor
  · intro forces
    have : ¬ N ≤ 2027 := fun h => lower (forces.mono h)
    omega
  · intro largeEnough
    exact upper.mono largeEnough

end UnitFractions
