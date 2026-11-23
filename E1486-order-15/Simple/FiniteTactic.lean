import Simple.FiniteBase
import Lean.Elab.Tactic.Simp

namespace E1486.Simple.Finite
open Lean Elab Tactic

/-- The larger cases expand more than the default `dsimp` step budget. -/
elab "unroll_graph" : tactic => do
  let stx ← `(tactic| dsimp [check, row, one, partner, ordered, geBits, nonSq, sqBits, swap,
    List.range, List.range.loop, List.all, List.map, List.flatMap, List.append])
  let { ctx, simprocs, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false) (kind := .dsimp)
  dsimpLocation (← ctx.setConfig {ctx.config with maxSteps := 3000000}) simprocs (.targets #[] true)

macro "check_graph" : tactic => `(tactic|
  (unroll_graph
   bv_decide (config := {timeout := 300, maxSteps := 3000000})))


/-- Some cases follow even without ordering the vertices. -/
macro "check_graph_unordered" : tactic => `(tactic|
  (apply Bool.and_eq_false_iff.mpr
   apply Or.inl
   dsimp [check, row, one, partner, List.range, List.range.loop, List.all]
   bv_decide (config := {timeout := 60})))

end E1486.Simple.Finite
