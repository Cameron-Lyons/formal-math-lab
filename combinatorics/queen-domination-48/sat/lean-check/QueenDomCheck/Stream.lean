/-
A streaming driver for Std's verified LRAT checker.

`Std.Tactic.BVDecide.LRAT.check` wants the whole proof as one `Array IntAction`, which costs about
8 bytes per number of the LRAT text (more than the text itself).  For proofs of several GB this is
too much, so this file re-plays the loop of `check` (`LRAT.Internal.check.go`) one step at a time:
the steps can then be produced, checked and thrown away chunk by chunk, and the memory is bounded by
the live clauses.

Nothing is re-implemented and nothing is assumed: each step calls the same Std functions as `check`
(`State.checkRup`, `State.checkRat`, `State.checkEmpty`, `State.add`, `State.deleteMany`), and the
soundness invariant is proved below from the same public Std lemmas that Std's own proof
`unsat_of_go` uses.  A `Verified cnf` value can only be built with a proof that a refutation of its
state is a refutation of `cnf`, and `Outcome.unsat` can only be built with a proof of `cnf.Unsat`.
The axioms used are printed at the end of this file.
-/
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Internal

namespace QueenDomCheck
open Std.Sat
open Std.Tactic.BVDecide.LRAT (IntAction)
open Std.Tactic.BVDecide.LRAT.Internal (State)

/-- A checker state, with the invariant that refuting it refutes the input formula. -/
structure Verified (cnf : CNF Nat) where
  state : State
  sound : CNF.Unsat state.toCNF → cnf.Unsat

/-- What one proof step leads to. -/
inductive Outcome (cnf : CNF Nat) where
  /-- the step was accepted and the proof goes on -/
  | next (v : Verified cnf)
  /-- the empty clause was derived: the formula is unsatisfiable -/
  | unsat (h : cnf.Unsat)
  /-- the step was rejected -/
  | rejected

namespace Verified

/-- The initial state: exactly the clauses of `cnf`, in order (ids 1, 2, ...). -/
def init (cnf : CNF Nat) : Verified cnf :=
  ⟨.ofCNF cnf, fun h => by simpa using h⟩

/-- The clause conversion of `LRAT.Internal.check.convertClause` (LRAT literal `±v` ↦ atom `v-1`). -/
def convertClause (clause : Array Int) : CNF.Clause Nat :=
  .ofLiterals <| clause.toList.filterMap fun int =>
    if int > 0 then some (int.natAbs - 1, true)
    else if int < 0 then some (int.natAbs - 1, false)
    else none

/-- One step of the loop of `LRAT.Internal.check`. -/
def step {cnf : CNF Nat} (v : Verified cnf) (a : IntAction) : Outcome cnf :=
  match a with
  | .addEmpty _ rupHints =>
    if h : v.state.checkEmpty rupHints then
      .unsat <| v.sound <|
        CNF.unsat_of_entails_clause_unsat (c := .empty) (by simp)
          (State.entails_clause_empty_of_checkEmpty h)
    else .rejected
  | .addRup _ clause rupHints =>
    let clause := convertClause clause
    if h : v.state.checkRup clause rupHints then
      .next ⟨v.state.add clause, fun hu => v.sound <|
        CNF.unsat_of_entails_unsat hu
          (State.entails_add_of_entails_clause (State.entails_clause_of_checkRup h))⟩
    else .rejected
  | .addRat _ clause pivot rupHints ratHints =>
    let clause := convertClause clause
    if h : v.state.checkRat clause ⟨pivot.1 - 1, pivot.2⟩ rupHints ratHints then
      .next ⟨v.state.add clause, fun hu => v.sound <|
        CNF.unsat_of_forall_exists (fun _ ha => State.unsat_of_unsat_of_checkRat h ha) hu⟩
    else .rejected
  | .del ids =>
    .next ⟨v.state.deleteMany ids, fun hu => v.sound <|
      CNF.unsat_of_entails_unsat hu State.entails_deleteMany⟩

/-- Result of running a batch of steps. -/
inductive BatchResult (cnf : CNF Nat) where
  /-- all steps accepted, no empty clause yet -/
  | more (v : Verified cnf)
  | unsat (h : cnf.Unsat)
  /-- step number `idx` of the batch was rejected -/
  | rejected (idx : Nat)

/-- Run `steps[idx:]`. -/
def runFrom {cnf : CNF Nat} (v : Verified cnf) (steps : Array IntAction) (idx : Nat) :
    BatchResult cnf :=
  if h : idx < steps.size then
    match v.step steps[idx] with
    | .next v => runFrom v steps (idx + 1)
    | .unsat h => .unsat h
    | .rejected => .rejected idx
  else .more v
termination_by steps.size - idx

end Verified

/--
A pure, whole-proof version (what the executable does chunk by chunk in `IO`): `true` iff the steps
of the chunks, run in order from the clauses of `cnf`, are all accepted up to an empty clause.
-/
def checkChunks (cnf : CNF Nat) (chunks : List (Array IntAction)) : Bool :=
  go (.init cnf) chunks
where
  go (v : Verified cnf) : List (Array IntAction) → Bool
    | [] => false
    | c :: cs =>
      match v.runFrom c 0 with
      | .more v => go v cs
      | .unsat _ => true
      | .rejected _ => false

theorem checkChunks_sound (cnf : CNF Nat) (chunks : List (Array IntAction))
    (h : checkChunks cnf chunks = true) : cnf.Unsat := by
  unfold checkChunks at h
  generalize Verified.init cnf = v at h
  induction chunks generalizing v with
  | nil => simp [checkChunks.go] at h
  | cons c cs ih =>
    unfold checkChunks.go at h
    split at h
    · exact ih _ h
    · assumption
    · contradiction

/-- The statement behind the default (non-streaming) mode, for reference: Std's own theorem. -/
theorem check_sound (proof : Array IntAction) (cnf : CNF Nat)
    (h : Std.Tactic.BVDecide.LRAT.check proof cnf = true) : cnf.Unsat :=
  Std.Tactic.BVDecide.LRAT.check_sound proof cnf h

end QueenDomCheck

/-- info: 'QueenDomCheck.checkChunks_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (info, drop warning) in
#print axioms QueenDomCheck.checkChunks_sound
