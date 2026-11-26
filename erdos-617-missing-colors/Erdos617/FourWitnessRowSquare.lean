module

public import Erdos617.SquareFourWitnesses
public import Erdos617.TwoLineExcess

@[expose] public section

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

/-- Deleting two intersecting full rows leaves a square where their colors
hit every r-set and at least four other colors can individually be avoided. -/
theorem exists_four_avoidable_row_square {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 100000≤r) (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c) :
    ∃ (i j : Fin r) (C D : Finset V), i≠j ∧ (colorGraph c i).IsNClique r C ∧
      (colorGraph c j).IsNClique r D ∧ (C∩D).card=1 ∧
      let U := (C∪D)ᶜ
      let d := fun e : Sym2 U => c (e.map Subtype.val)
      U.card=(r-1)^2+1 ∧ rankOn (colorGraph c i) U≤r-1 ∧ rankOn (colorGraph c j) U≤r-1 ∧
      4≤(univ.filter fun k => ¬HitsPalette d (r-1) {k}).card := by
  obtain ⟨i,j,C,D,ne,fullC,fullD,meet,sz,ri,rj⟩ := exists_two_line_square (by omega) hn c hb
  let U := (C∪D)ᶜ
  have out : Disjoint U (C∪D) := disjoint_compl_left
  refine ⟨i,j,C,D,ne,fullC,fullD,meet,sz,ri,rj,?_⟩
  exact four_avoidable_of_good_edge_excess (by omega) hn c hb U sz i j
    (fun _ ki kj cap no => two_line_good_color_excess hr hb ki kj C D U fullC fullD meet out sz cap no)

end Erdos617
