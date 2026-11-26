module

public import Involution
public import MultiplierCore
public import Order17BoundaryGeometry
public import Order17Coordinates
public import Abelian
public import PrimeSymmetry
public import Steiner

@[expose] public section

/-!
# Symmetry exclusions for Erdős problem 835 at k = 16

This library includes global symmetry exclusions, the reduction to a cyclic
20-point quadruple system, and obstructions to particular local designs.
-/

namespace Erdos835

/-- The upstream existential at k = 16, written out so that the link to our
coloring predicate is checked by definitional equality. -/
theorem property16_formulation :
    (let k : ℕ := 16
     let K := {s : Finset (Fin (2 * k)) // s.card = k}
     ∃ c : K → Fin (k + 1), ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
       Finset.image c {s : K | s.val ⊂ A} = (Finset.univ : Finset (Fin (k + 1)))) ↔
      ∃ c : Block → Fin 17, Rainbow c := Iff.rfl

end Erdos835
