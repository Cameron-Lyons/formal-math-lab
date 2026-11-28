/-
The formula of a case, built so that the base formula of a deficit vector is converted once and shared
by all cases with that deficit vector.

`QueenDomSat.caseFormula n k cs` is, by definition,
`toCNF ((mkBase n k dR dC dT dS).cls ++ (caseExtra (mkBase n k dR dC dT dS) ml mr mb mt).1)`: evaluated
literally, it would rebuild and convert the ~236,000 clauses of `enc.Base` for every case.  Here

  * `BaseCNF n k` holds `toCNF (mkBase n k dR dC dT dS).cls` for one deficit vector, together with the
    proof that it is this value;
  * `Prepared n k cs` holds a formula `cnf` together with a proof of `caseFormula n k cs = cnf`;
  * `prepare` builds a `Prepared n k cs` from a `BaseCNF` with the deficits of `cs`: it appends the
    converted frame-dependent clauses to the shared base formula (`QueenDomSat.caseCNF_eq`).

Everything in this file is kernel-checked: a `Prepared n k cs` cannot be built without the proof
that its formula is `caseFormula n k cs`, whatever the compiled code computes.  The fields `emptyId`
are hints for the untrusted LRAT normaliser and occur in no statement.
-/
import QueenDomSat

namespace QueenDomCheck
open QueenDomSat
open Std.Sat

/-- The frame-dependent clauses of the case `cs`: `enc.case_extra(B, cs)[0]`, computed without the
clause array of `B` (only `B.nv = baseNv ...` is needed). -/
def extraClauses (n k : Nat) (cs : CaseT) : List Clause :=
  (extraGroup n k cs.dR cs.dC cs.dT cs.dS cs.ml (n - 1 - cs.mr) cs.mb (n - 1 - cs.mt)
    (baseNv n k cs.dR cs.dC cs.dT cs.dS)).cls

theorem caseExtra_eq (n k : Nat) (cs : CaseT) :
    (caseExtra (cs.base n k) cs.ml cs.mr cs.mb cs.mt).1 = (extraClauses n k cs).toArray := rfl

/-- 1-based position of the first empty clause of a clause list, 0 if there is none.  (A hint for
the LRAT normaliser: drat-trim writes an empty proof for a formula that contains the empty clause.) -/
def firstEmpty (cls : List Clause) : Nat :=
  go cls 1
where
  go : List Clause → Nat → Nat
    | [], _ => 0
    | c :: cs, i => if c.isEmpty then i else go cs (i + 1)

/-- The converted base formula `enc.Base(n, k, (dR, dC, dT, dS))` of one deficit vector. -/
structure BaseCNF (n k : Nat) where
  dR : Nat
  dC : Nat
  dT : Nat
  dS : Nat
  cnf : CNF Nat
  cnf_eq : cnf = toCNF (mkBase n k dR dC dT dS).cls
  /-- untrusted hint: 1-based position of an empty clause of the base formula, 0 if it has none -/
  emptyId : Nat

/-- Build and convert the base formula of the deficit vector `(dR, dC, dT, dS)`. -/
def BaseCNF.build (n k dR dC dT dS : Nat) : BaseCNF n k :=
  let cls := (mkBase n k dR dC dT dS).cls
  { dR := dR, dC := dC, dT := dT, dS := dS
    cnf := toCNF cls
    cnf_eq := rfl
    emptyId := firstEmpty cls.toList }

/-- The base formula `b` is the one of the deficit vector of `cs`. -/
def BaseCNF.Matches {n k : Nat} (b : BaseCNF n k) (cs : CaseT) : Prop :=
  b.dR = cs.dR ∧ b.dC = cs.dC ∧ b.dT = cs.dT ∧ b.dS = cs.dS

instance {n k : Nat} (b : BaseCNF n k) (cs : CaseT) : Decidable (b.Matches cs) := by
  unfold BaseCNF.Matches; infer_instance

theorem BaseCNF.matches_build (n k : Nat) (cs : CaseT) :
    (BaseCNF.build n k cs.dR cs.dC cs.dT cs.dS).Matches cs := ⟨rfl, rfl, rfl, rfl⟩

/-- The formula of a case is the shared base formula followed by the converted frame-dependent
clauses. -/
theorem caseFormula_eq {n k : Nat} (b : BaseCNF n k) (cs : CaseT) (h : b.Matches cs) :
    caseFormula n k cs = b.cnf ++ toCNF (extraClauses n k cs).toArray := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [caseFormula, caseCNF_eq, caseExtra_eq, b.cnf_eq, h1, h2, h3, h4]
  rfl

/-- A formula that is proved to be the formula of the case `cs`. -/
structure Prepared (n k : Nat) (cs : CaseT) where
  cnf : CNF Nat
  cnf_eq : caseFormula n k cs = cnf
  /-- untrusted hint: 1-based position of an empty clause of `cnf`, 0 if it has none -/
  emptyId : Nat

/-- The formula of `cs` from the shared base formula of its deficit vector. -/
def prepare {n k : Nat} (b : BaseCNF n k) (cs : CaseT) (h : b.Matches cs) : Prepared n k cs :=
  let extra := extraClauses n k cs
  { cnf := b.cnf ++ toCNF extra.toArray
    cnf_eq := caseFormula_eq b cs h
    emptyId :=
      if b.emptyId != 0 then b.emptyId
      else
        let e := firstEmpty extra
        if e != 0 then b.cnf.clauses.size + e else 0 }

/-- Transport of a refutation to the statement about `caseFormula`. -/
theorem Prepared.unsat {n k : Nat} {cs : CaseT} (p : Prepared n k cs) (h : p.cnf.Unsat) :
    (caseFormula n k cs).Unsat := p.cnf_eq ▸ h

end QueenDomCheck
