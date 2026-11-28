module

public import Wall133.OddRootedGrowth
public import Wall133.FifthConfiguration

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Average neighborhood independence five forces eight vertices on an
induced path, including when triangles or five-cycles are present. -/
theorem eight_le_path_of_five_le_average (h4 : NoFourCycle G) (avg : (5:ℝ)≤l G) :
    8 ≤ G.path := by
  obtain ⟨S,P,four,high,minimum⟩ := exists_five_rooted_dense_core h4 avg
  exact (eight_of_five_chain P four high minimum).trans (G.path_induce_le (S:Set V))

/-- The fifth floor band holds through radius three. -/
theorem radius_add_five_le_path_of_radius_le_three (h4 : NoFourCycle G)
    (hr : G.radius.toNat≤3) (avg : (5:ℝ)≤l G) : G.radius.toNat+5 ≤ G.path := by
  have := eight_le_path_of_five_le_average h4 avg
  omega

end Wall133
