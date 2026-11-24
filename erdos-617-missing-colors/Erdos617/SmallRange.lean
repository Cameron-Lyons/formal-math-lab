import Erdos617.StrictHalfRange
import Erdos617.RankObstruction
import Mathlib.Tactic.IntervalCases

namespace Erdos617

/-- The half-range and density estimates exclude every balanced coloring on
the conjectured number of vertices for three through six colors. -/
theorem missing_of_at_most_six_colors {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 3 ≤ r) (hmax : r ≤ 6) (hV : Fintype.card V = r^2+1) (c : Sym2 V → Fin r) :
    ∃ (S : Finset V) (k : Fin r), S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k := by
  by_contra hn
  have hb := balanced_of_no_witness c hn
  obtain ⟨k, t, S, _, ht, h⟩ := exists_minimalObstruction_ceil_half hr hV c hb
  have htwo := h.two_le_parameter hr hb (by omega)
  have hbound := h.rank_parameter_bound hr hb (by omega)
  have hthree : t ≤ 3 := by omega
  interval_cases t <;> interval_cases r <;> norm_num at *

end Erdos617
