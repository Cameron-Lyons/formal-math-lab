module

public meta import Lean.Data.Json
public meta import Lean.Elab.Term
public import Std.Tactic.BVDecide.Reflect
meta import Std.Tactic.BVDecide.Reflect
import all Std.Sat.CNF.Sat

@[expose] public section

/-! # A certified unsatisfiable CNF for the order-eight multiplier obstruction

The clauses use zero-based atoms and `true` for a positive literal. The proof
is an LRAT derivation checked by Lean's standard library. -/

namespace Erdos835.MultiplierSAT

open Lean Std.Sat Std.Tactic.BVDecide

abbrev Lit := Nat × Bool

def clauseTrue (a : Nat → Bool) (C : List Lit) : Prop := ∃ l ∈ C, a l.1 = l.2

def toCNF (cs : List (List Lit)) : CNF Nat :=
  ⟨(cs.map CNF.Clause.ofLiterals).toArray⟩

private theorem represented (cs : List (List Lit)) (a : Nat → Bool)
    (h : ∀ c ∈ cs, clauseTrue a c) : (toCNF cs).eval a = true := by
  simp only [toCNF, CNF.eval, List.all_toArray, List.all_map, List.all_eq_true]
  intro c hc
  obtain ⟨⟨v,p⟩, hm, eq⟩ := h c hc
  simpa only [Function.comp_apply, CNF.Clause.eval, CNF.Clause.literals_ofLiterals,
    List.any_eq_true] using (show ∃ x ∈ c, (a x.1 == x.2) = true from ⟨(v,p),hm, beq_iff_eq.mpr eq⟩)

/-- A successful check by Lean's LRAT verifier rules out every truth assignment. -/
theorem of_verified (cs : List (List Lit)) (trace : String)
    (h : Reflect.verifyCert (toCNF cs) trace = true) (a : Nat → Bool) :
    ¬ ∀ C ∈ cs, clauseTrue a C := by
  intro allTrue
  have negative := Reflect.verifyCert_correct _ _ h a
  rw [represented _ a allTrue] at negative
  contradiction

private meta def fileFromSource (relative : String) : Elab.Term.TermElabM System.FilePath := do
  let source := System.FilePath.mk (← readThe Lean.Core.Context).fileName
  return source.parent.getD "." / relative

/-- Embed a JSON array of clauses as a list of zero-based atom/polarity pairs. -/
elab "satClausesFrom% " path:str : term => do
  let raw ← IO.FS.readFile (← fileFromSource path.getString)
  let data ← IO.ofExcept (Json.parse raw >>= fromJson? (α := List (List Lit)))
  return toExpr data

/-- Embed a textual LRAT certificate relative to the source file. -/
elab "satTraceFrom% " path:str : term => do
  return mkStrLit (← IO.FS.readFile (← fileFromSource path.getString))

set_option maxRecDepth 20000 in
def certificateClauses : List (List Lit) := satClausesFrom% "certificates/multiplier8-sat.json"

private def traceFile : String := satTraceFrom% "certificates/multiplier8.lrat"

private theorem trace_valid : Reflect.verifyCert (toCNF certificateClauses) traceFile = true := by
  native_decide

theorem unrealizable (a : Nat → Bool) : ¬ ∀ C ∈ certificateClauses, clauseTrue a C :=
  of_verified certificateClauses traceFile trace_valid a

end Erdos835.MultiplierSAT
