import Ramsey556.Biclique13
import Ramsey556.Connected33
import Ramsey556.DenseCore
import Ramsey556.FourteenResult
import Ramsey556.Saturated33
import Ramsey556.ThreeShore

namespace Ramsey556

/-- Every red K₃,₁₇, and likewise a copy in either other color, forces a monochromatic C₉. -/
theorem monoC9_of_three_seventeen (c : Coloring 33) (r : Fin 3)
    (a : Fin 3 → Fin 33) (b : Fin 17 → Fin 33)
    (ai : ∀ ⦃i j⦄, a i = a j → i = j) (bi : ∀ ⦃i j⦄, b i = b j → i = j)
    (apart : ∀ i j, a i ≠ b j) (cross : ∀ i j, c.edge (a i) (b j) = r) : HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  exact free (BicliqueObstruction.hasMonoC9_of_three_shore (m := 15) c r (by decide)
    a b (@ai) (@bi) apart cross (fun v vi => allColorsOn15_of_free free v (@vi) r))

/-- If some fourteen vertices miss a color, the classified eight-plus-six
template occurs there, with the three specified exterior vertices. -/
def HasWideFourteen (c : Coloring 33) : Prop :=
  ∃ (r : Fin 3) (v : Fin 14 → Fin 33), (∀ ⦃i j⦄, v i = v j → i = j) ∧ WideFourteen c v r

private theorem local_cases {c : Coloring 33} (free : ¬ HasMonoC9 c) :
    AllColorsOn 14 c ∨ HasWideFourteen c := by
  classical
  by_cases wide : HasWideFourteen c
  · exact Or.inr wide
  left
  intro v vi r
  apply Classical.byContradiction
  intro missing
  exact wide ⟨r,v,vi,wideFourteen_of_missing_color c free v vi r
    (fun i j ne e => missing ⟨i,j,ne,e⟩)⟩

/-- The first remaining branch has all three independence numbers at most 13.
In the other branch some color has independence number 14 and a classified
eight-plus-six witness. One may require connectivity in all three colors and
a minimum-degree-seven subgraph of order at least twenty in a heavy color. -/
theorem k33_iff_final_two_cases :
    K33Claim ↔ ∀ c : Coloring 33, AllColorsConnected c → Connected33.SaturatedOffBridges c →
      (∃ k, 176 ≤ CycleStructure.tally c k ∧ HasSevenCoreOfOrder c k 20) →
      (AllColorsOn 14 c → HasMonoC9 c) ∧
      (AllColorsOn 15 c → HasWideFourteen c → HasMonoC9 c) := by
  refine ⟨fun h c _ _ _ => ⟨fun _ => h c,fun _ _ => h c⟩,?_⟩
  intro cases
  apply Connected33.k33_iff_connected_saturated.mpr
  intro c connected saturated
  apply Classical.byContradiction
  intro free
  obtain ⟨first,second⟩ := cases c connected saturated (some_twentyVertexSevenCore free)
  rcases local_cases free with all | wide
  · exact free (first all)
  · exact free (second (allColorsOn15_of_free free) wide)

/-- In the ordered saturation reduction the saturated red graph itself
has a large seven-core. -/
theorem saturated_red_has_seven_core {c : Coloring 33} (free : ¬ HasMonoC9 c)
    (many : 176 ≤ CycleStructure.tally c 0) : HasSevenCoreOfOrder c 0 20 :=
  twentyVertexSevenCore (by omega) (fun h => free ⟨0,h⟩)

end Ramsey556
