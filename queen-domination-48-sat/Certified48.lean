import Queens48.Gamma48

/-!
# `γ(Q_48) = i(Q_48) = 25`, with the certificate check recorded as an explicit axiom

Everything in the library `Queens48` is proved from `propext`, `Classical.choice`, `Quot.sound` alone.
In particular (`Queens48/Gamma48.lean`):

    theorem gamma_48_eq_25_of_formulas_unsat
        (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) :
        gamma 48 = 25

The hypothesis `H` (47,580 explicit CNF formulas, defined in Lean in `lean-sat`, are unsatisfiable) is
NOT proved in the kernel: the certificates are 148 GB of LRAT text.  It was established by running the
compiled Lean program `qdcheck` (`lean-check`), which checks an LRAT certificate of every formula
with the verified LRAT checker of Lean's standard library and can only report success by constructing a
value of type `PLift H`:

    $ qdcheck 48 24 runs/d_48_24.jsonl.lrat --jobs 5
    s ALL VERIFIED n=48 k=24 cases=47580

(records: `data/frame/lean_check_48_24.summary.json`, `lean_check_48_24.jsonl`).  Accepting that run
means trusting the Lean compiler and runtime, as `native_decide` does, but here the fact enters as the
named axiom below, so that `#print axioms` shows it.

This file is deliberately NOT part of the library `Queens48` (it is not imported by `Queens48.lean`):
check it with `lake env lean Certified48.lean`.
-/

namespace QueenDom

/-- **Computational fact, established outside the kernel** by the run of `qdcheck 48 24` described
above: the formula of every case of the case list `L(48, 24)` is unsatisfiable. -/
axiom formulas_48_24_unsat :
    ∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat

/-- **The queen domination number of the `48 × 48` board is `25`** (modulo `formulas_48_24_unsat`). -/
theorem gamma_48 : gamma 48 = 25 := gamma_48_eq_25_of_formulas_unsat formulas_48_24_unsat

/-- **The independent queen domination number of the `48 × 48` board is `25`** (modulo
`formulas_48_24_unsat`). -/
theorem igamma_48 : igamma 48 = 25 := igamma_48_eq_25_of_formulas_unsat formulas_48_24_unsat

/-- No 24 queens dominate the `48 × 48` board (modulo `formulas_48_24_unsat`). -/
theorem twentyfive_le_card (D : Finset (Sq 48)) (hD : Dominating D) : 25 ≤ D.card :=
  twentyfive_le_card_of_formulas_unsat formulas_48_24_unsat D hD

end QueenDom

#print axioms QueenDom.gamma_48
#print axioms QueenDom.igamma_48
#print axioms QueenDom.twentyfive_le_card
#print axioms QueenDom.gamma_48_eq_25_of_formulas_unsat
#print axioms QueenDom.igamma_48_eq_25_of_formulas_unsat
#print axioms QueenDom.gamma_48_le
#print axioms QueenDom.igamma_48_le
