import EvenUnitFractions.Lower
import EvenUnitFractions.Upper

namespace EvenUnitFractions

/-- For every even integer `k ≥ 4`, every red-blue coloring of `{1, ..., N}` contains a
monochromatic solution to `1/x₁ + ... + 1/xₖ = 1/y` (with repetitions allowed)
if and only if `3 * k * k ≤ N`.

This settles the even case of Gaiser and Ramezanpour's Conjecture 1.3 (`arXiv:2607.04373`)
and Arevalo's Conjecture B: `f₂(k) = 3k²` for every even `k ≥ 4`. -/
theorem forces_iff {k : Nat} (heven : k % 2 = 0) (hk : 4 ≤ k) (N : Nat) :
    Forces k N ↔ 3 * k * k ≤ N := by
  constructor
  · intro forces
    have : ¬ N ≤ 3 * k * k - 1 := fun h => lower (by omega) (forces.mono h)
    omega
  · intro largeEnough
    exact (upper heven hk).mono largeEnough

end EvenUnitFractions
