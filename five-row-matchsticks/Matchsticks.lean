import Matchsticks.Geometry
import Matchsticks.Upper
import Matchsticks.Lower

/-! # Breaking every rectangle in a five-row grid

Run `lake build` from the directory containing this file. The theorem refers
to the four sides of a rectangle in lattice coordinates. Both existence of
a board of the stated cost and optimality over all boards are asserted.
-/
namespace Matchsticks

/-- Among all five-row boards of width `n` with every rectangular outline
broken, `k` is attained and is a lower bound on the number of erased sticks. -/
def MinimumErasures (n k : Nat) : Prop :=
  (∃ b : Board, b.width = n ∧ ¬ b.HasRectangle ∧ b.cost = k) ∧
  ∀ b : Board, b.width = n → ¬ b.HasRectangle → k ≤ b.cost

private theorem minimum_target (n : Nat) (hn : 0 < n) :
    MinimumErasures n (target n) := by
  obtain ⟨b, width, safe, cost⟩ := attainable n hn
  refine ⟨⟨b, width, no_rectangle_of_safe b safe, cost⟩, ?_⟩
  intro board width noRectangle
  simpa only [width] using lower board (by omega) noRectangle

/-- The exact minimum is five at width one and ⌊(10n + 4)/3⌋ at every width n ≥ 2.
Natural-number division in Lean is floor division. -/
theorem five_row_matchstick_theorem :
    MinimumErasures 1 5 ∧
    ∀ n : Nat, 2 ≤ n → MinimumErasures n ((10 * n + 4) / 3) := by
  refine ⟨minimum_target 1 (by decide), ?_⟩
  intro n hn
  simpa [target, show n ≠ 1 by omega] using minimum_target n (by omega)

end Matchsticks
