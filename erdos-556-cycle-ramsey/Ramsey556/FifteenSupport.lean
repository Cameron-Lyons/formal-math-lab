import Ramsey556.Fifteen
import Ramsey556.FifteenResult

namespace Ramsey556

/-- The earlier support statement follows since a red-independent 15-set
already forces a monochromatic nine-cycle. -/
theorem anchorSupport_of_independent15 (c : Coloring 33) (free : ¬ HasMonoC9 c)
    (v : Fin 15 → Fin 33) (vi : ∀ ⦃i j⦄, v i = v j → i = j)
    (absent : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ 0) : Nonempty (AnchorSupport c) :=
  (free (monoC9_of_independent15 c v (@vi) 0 absent)).elim

end Ramsey556
