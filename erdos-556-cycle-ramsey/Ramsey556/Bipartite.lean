import Ramsey556.Basic
import Ramsey556.VertexSets

namespace Ramsey556

/-- The edges of color `k` admit a bipartition. The diagonal is ignored. -/
def IsBipartiteColor {n : Nat} (c : Coloring n) (k : Fin 3) : Prop :=
  ∃ side : Fin n → Bool, ∀ u v, u ≠ v → c.edge u v = k → side u ≠ side v

/-- One side of a bipartition on more than 2m vertices contains an independent
set of m+1 vertices in that color. -/
theorem IsBipartiteColor.independent_set {n m k} {c : Coloring n}
    (bip : IsBipartiteColor c k) (room : 2 * m < n) :
    ∃ v : Fin (m+1) → Fin n, Function.Injective v ∧ ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ k := by
  obtain ⟨side, cut⟩ := bip
  obtain ⟨v, _, inj, same⟩ := select_side side room
  exact ⟨v, inj, fun i j ne edge => cut _ _ (inj.ne ne) edge ((same i).trans (same j).symm)⟩

theorem IsBipartiteColor.induce {m n k} {c : Coloring n} {v : Fin m → Fin n}
    (bip : IsBipartiteColor c k) (inj : Function.Injective v) : IsBipartiteColor (c.induce v) k := by
  obtain ⟨side, cut⟩ := bip
  exact ⟨side ∘ v, fun _ _ ne => cut _ _ (inj.ne ne)⟩

/-- Two bipartite color classes force a third-color clique on nine vertices.
The two bipartitions divide 33 vertices into four cells. -/
theorem hasMonoC9_of_two_bipartite (c : Coloring 33) {r s : Fin 3} (hrs : r ≠ s)
    (hr : IsBipartiteColor c r) (hs : IsBipartiteColor c s) : HasMonoC9 c := by
  obtain ⟨v, vi, noR⟩ := hr.independent_set (m := 16) (by decide)
  obtain ⟨w, wi, noS⟩ := (hs.induce vi).independent_set (m := 8) (by decide)
  have third : ∀ r s : Fin 3, r ≠ s → ∃ t, ∀ x : Fin 3, x ≠ r → x ≠ s → x = t := by decide
  obtain ⟨t, color⟩ := third r s hrs
  refine ⟨t, v ∘ w, vi.comp wi, ?_⟩
  intro i
  have next : i ≠ i+1 := (by decide : ∀ j : Fin 9, j ≠ j+1) i
  exact color _ (noR _ _ (wi.ne next)) (noS _ _ next)

end Ramsey556
