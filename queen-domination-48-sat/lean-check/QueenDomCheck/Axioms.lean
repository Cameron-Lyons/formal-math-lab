/-
The axioms behind the checker, verified at build time: each `#guard_msgs` below fails the build if
the list of axioms changes (in particular if `sorryAx`, or `Lean.ofReduceBool` / `Lean.trustCompiler`
from `native_decide`, appeared).
-/
import QueenDomCheck.Verify

/-- info: 'QueenDomCheck.checkChunks_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueenDomCheck.checkChunks_sound

/-- info: 'QueenDomCheck.Verified.runFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueenDomCheck.Verified.runFrom

/-- info: 'QueenDomCheck.caseFormula_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms QueenDomCheck.caseFormula_eq

/-- info: 'QueenDomCheck.Prepared.unsat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueenDomCheck.Prepared.unsat

/-- info: 'QueenDomCheck.forall_of_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms QueenDomCheck.forall_of_covers

/-- info: 'QueenDomCheck.verifyCase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueenDomCheck.verifyCase

/-- info: 'QueenDomCheck.verifyList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueenDomCheck.verifyList

/-- info: 'QueenDomCheck.verifyAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QueenDomCheck.verifyAll
