import Ramsey556.FourteenOctet
import Ramsey556.CliqueOverlap

namespace Ramsey556

/-- Fifteen vertices on which one color is absent force a monochromatic nine-cycle. -/
theorem monoC9_of_independent15 (c : Coloring 33) (v : Fin 15 → Fin 33)
    (inj : Function.Injective v) (r : Fin 3)
    (absent : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ r) : HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  obtain ⟨removed, hitsEveryClique⟩ :=
    CliqueOverlap.hitting_vertex (c.induce v) (mt (HasMonoC9.of_induce inj) free)
  let keep := Fifteen.skip removed
  have keepInj : Function.Injective keep := Fifteen.skip_injective removed
  obtain ⟨color, clique, cliqueInj, edges⟩ :=
    octet_of_missing_color14 c free (v ∘ keep) (inj.comp keepInj) r
      (fun _ _ ne => absent _ _ (keepInj.ne ne))
  obtain ⟨i, hit⟩ := hitsEveryClique color (keep ∘ clique) (keepInj.comp cliqueInj) edges
  exact Fifteen.skip_ne removed (clique i) hit

/-- Every induced subgraph of this order uses each of the three edge colors. -/
def AllColorsOn (m : Nat) (c : Coloring 33) : Prop :=
  ∀ (v : Fin m → Fin 33), Function.Injective v →
    ∀ r : Fin 3, ∃ i j, i ≠ j ∧ c.edge (v i) (v j) = r

theorem allColorsOn15_of_free {c : Coloring 33} (free : ¬ HasMonoC9 c) : AllColorsOn 15 c := by
  intro v vi r
  apply Classical.byContradiction
  intro missing
  exact free (monoC9_of_independent15 c v vi r (fun i j ne e => missing ⟨i,j,ne,e⟩))

/-- The unrestricted question reduces to colorings whose three independence numbers are at most 14. -/
theorem k33_iff_independence_at_most_14 :
    K33Claim ↔ ∀ c : Coloring 33, AllColorsOn 15 c → HasMonoC9 c := by
  refine ⟨fun h c _ => h c, fun h c => Classical.byContradiction (fun free => ?_)⟩
  exact free (h c (allColorsOn15_of_free free))

/-- If one color becomes bipartite after four vertex deletions, a monochromatic C₉ exists. -/
theorem monoC9_of_bipartite_after_four_deletions (c : Coloring 33) (v : Fin 29 → Fin 33)
    (inj : Function.Injective v) (r : Fin 3)
    (bip : IsBipartiteColor (c.induce v) r) : HasMonoC9 c := by
  obtain ⟨u, ui, absent⟩ := bip.independent_set (m := 14) (by decide)
  exact monoC9_of_independent15 c (v ∘ u) (inj.comp ui) r absent

end Ramsey556
