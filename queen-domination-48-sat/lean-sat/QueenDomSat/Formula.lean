/-
The formula of a case of the case list: `Encode` applied to a `CaseT`.
-/
module

public import QueenDomSat.Encode
public import QueenDomSat.Cases

@[expose] public section

namespace QueenDomSat

/-- The base formula `enc.Base(n, k, (dR, dC, dT, dS))` of a case. -/
def CaseT.base (n k : Nat) (cs : CaseT) : Base := mkBase n k cs.dR cs.dC cs.dT cs.dS

/-- The CNF of the case `cs` for `(n, k)`: the clauses of the DIMACS file
`enc.dimacs(B, *enc.case_extra(B, cs))`, `B = enc.Base(n, k, cs[4:])`, in the order of the file. -/
def caseFormula (n k : Nat) (cs : CaseT) : Std.Sat.CNF Nat :=
  caseCNF (cs.base n k) cs.ml cs.mr cs.mb cs.mt

/-- The DIMACS text of the case `cs` for `(n, k)`: `enc.dimacs(B, *enc.case_extra(B, cs))`. -/
def caseDimacs (n k : Nat) (cs : CaseT) : String :=
  let B := cs.base n k
  let E := caseExtra B cs.ml cs.mr cs.mb cs.mt
  dimacs B E.1 E.2

end QueenDomSat
