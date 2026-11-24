import Lean
import E670.Encoding

/-!
# Refuting a formula case by case

A *cube* is a list of literals.  `Refutes F cubes` says that the formula `F` has no model inside
any of the cubes, and `unsat_of_cubes` concludes that `F` has no model at all once `F` together
with the negations of all the cubes has been refuted as well.

The tactic `refute` proves `Refutes F cubes`.  It runs CaDiCaL, the SAT solver that ships with
Lean, once per cube.  The solver's answers are not trusted: they are LRAT certificates, which
`Std.Tactic.BVDecide.Reflect.verifyCert`, the verified checker behind `bv_decide`, checks under
`native_decide`.  The choice of cubes is not trusted either.
-/

namespace E670

open Std.Sat Std.Tactic.BVDecide

abbrev Cube := List Lit

/-- No assignment satisfies every clause in the list. -/
def Unsat (F : List Cl) : Prop := ∀ α, ¬ ∀ c ∈ F, csat α c = true

/-- A cube as unit clauses. -/
def units (c : Cube) : List Cl := c.map fun l => [l]

/-- The clause saying that an assignment is outside a cube. -/
def negCube (c : Cube) : Cl := c.map fun l => (l.1, !l.2)

/-- `F` has no model inside any of the cubes. -/
def Refutes (F : List Cl) (cubes : List Cube) : Prop := ∀ c ∈ cubes, Unsat (F ++ units c)

/-- Check one LRAT certificate per cube. -/
def checkCubes (F : List Cl) (cubes : List Cube) (certs : List String) : Bool :=
  (List.range cubes.length).all fun i =>
    Reflect.verifyCert (toCNF (F ++ units (cubes.getD i []))) (certs.getD i "")

theorem refutes_of_check (F : List Cl) (cubes : List Cube) (certs : List String)
    (h : checkCubes F cubes certs = true) : Refutes F cubes := by
  intro c hc α hα
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hcert := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hcert
  exact CNF.unsat_iff_not_sat.mp (Reflect.verifyCert_correct _ _ hcert) α (sat_toCNF hα)

/-- Lists of cubes that are refuted one by one are refuted together. -/
theorem Refutes.flatten {F : List Cl} {parts : List (List Cube)}
    (h : ∀ k < parts.length, Refutes F parts[k]!) : Refutes F parts.flatten := by
  intro c hc
  obtain ⟨p, hp, hcp⟩ := List.mem_flatten.mp hc
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
  exact (getElem!_pos parts k hk ▸ h k hk) c hcp

/--
If every cube is refuted and no model of `F` avoids all the cubes, `F` is unsatisfiable.
The second hypothesis is stated with the empty cube, which adds nothing to a formula, so that
`refute` proves it too.
-/
theorem unsat_of_cubes {F : List Cl} {cubes : List Cube}
    (hcubes : Refutes F cubes) (hcover : Refutes (F ++ cubes.map negCube) [[]]) : Unsat F := by
  intro α hα
  apply hcover [] (List.mem_singleton.mpr rfl) α
  simp only [units, List.map_nil, List.append_nil, List.forall_mem_append, List.forall_mem_map]
  refine ⟨hα, fun c hc => Classical.byContradiction fun hout => ?_⟩
  -- otherwise `α` would be a model of `F` inside the refuted cube `c`
  refine hcubes c hc α (List.forall_mem_append.mpr ⟨hα, fun cl hcl => ?_⟩)
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hcl
  have hl' : ¬ (α l.1 == !l.2) = true := fun hl' =>
    hout (List.any_eq_true.mpr ⟨_, List.mem_map_of_mem hl, hl'⟩)
  simpa [csat] using hl'

open Lean Elab Meta Tactic in
/--
`refute` proves a goal `Refutes F cubes`.  It evaluates `F` and `cubes`, runs CaDiCaL on `F`
extended by each cube in turn, and closes the goal with `refutes_of_check`, leaving it to
`native_decide` to check the certificates.  These end up as string literals in the proof.
-/
elab "refute" : tactic => withMainContext do
  let_expr Refutes F cubes := ← getMainTarget
    | throwError "refute: the goal is not `Refutes F cubes`"
  let clauses ← unsafe evalExpr (List Cl) (← inferType F) F
  -- the solver that `bv_decide` would use
  let solver := (← Lean.Meta.Tactic.BVDecide.TacticContext.new "" {}).solver
  let certs ← (← unsafe evalExpr (List Cube) (← inferType cubes) cubes).mapM fun c =>
    IO.FS.withTempFile fun _ lrat => do
      match ← Lean.Meta.Tactic.BVDecide.runExternal (toCNF (clauses ++ units c)) solver lrat
          (trimProofs := true) (timeout := 3600) (binaryProofs := true) (solverMode := .proof) with
      | .ok cert => pure cert
      | .error _ => throwError "refute: the formula has a model in the cube {repr c}"
  let certs ← Term.exprToSyntax (toExpr certs)
  evalTactic (← `(tactic| exact refutes_of_check _ _ $certs (by native_decide)))

end E670
