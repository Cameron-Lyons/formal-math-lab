import Queens48

/-! Axiom report for Layer 2 (the soundness of the CNF encoding, `Queens48/*.lean`) and for the
`n = 48` statements.  Run with `lake env lean Axioms48.lean`; the output is saved in `AXIOMS48.txt`.

Expected: only `propext`, `Classical.choice`, `Quot.sound` (or a subset).  In particular no `sorryAx`,
no `Lean.ofReduceBool` and no `Lean.trustCompiler` (no `native_decide`).
The last command checks mechanically every declaration of the modules `Queens48.*` and
`QueenDomSat.*` (the encoder package `lean-sat`). -/

-- the sequential counter (Framework.lean)
#print axioms QueenDom.Sat.atmostSeq_sound
#print axioms QueenDom.Sat.atmost_sound
#print axioms QueenDom.Sat.exactly_sound
-- the base formula (Base.lean)
#print axioms QueenDom.Sat.holds_defCls
#print axioms QueenDom.Sat.holds_domCls
#print axioms QueenDom.Sat.holds_amoCls
#print axioms QueenDom.Sat.Kind.exactly_sound
#print axioms QueenDom.Sat.base_sound
-- the waste literals (Waste.lean)
#print axioms QueenDom.Sat.waste_sound
#print axioms QueenDom.Sat.count_wasteValues
-- the frame-dependent clauses (Extra.lean)
#print axioms QueenDom.Sat.holds_frameCls
#print axioms QueenDom.Sat.groupF_sound
#print axioms QueenDom.Sat.groupV_sound
#print axioms QueenDom.Sat.groupH_sound
#print axioms QueenDom.Sat.extra_sound
-- soundness of the encoding of a case, lower bounds for γ (Sound.lean)
#print axioms QueenDom.Sat.caseFormula_sat_of_caseSat
#print axioms QueenDom.Sat.enumCases_map_toT
#print axioms QueenDom.Sat.card_lt_of_formulas_unsat
#print axioms QueenDom.Sat.lt_gamma_of_formulas_unsat
#print axioms QueenDom.Sat.lt_gamma_of_lrat_check
-- n = 48 (Gamma48.lean)
#print axioms QueenDom.independent_iff_isIndepSet
#print axioms QueenDom.igamma_le
#print axioms QueenDom.gamma_le_igamma
#print axioms QueenDom.q48i_card
#print axioms QueenDom.q48i_dominating
#print axioms QueenDom.q48i_independent
#print axioms QueenDom.gamma_48_le
#print axioms QueenDom.igamma_48_le
#print axioms QueenDom.twentyfive_le_card_of_formulas_unsat
#print axioms QueenDom.gamma_48_eq_25_of_formulas_unsat
#print axioms QueenDom.igamma_48_eq_25_of_formulas_unsat
#print axioms QueenDom.gamma_48_eq_25_of_lrat_check
-- the case list of the run records, n = 48 (Cases48.lean, Cases48Pieces.lean)
#print axioms QueenDom.cases48_length
#print axioms QueenDom.enumFrames_48_24_length
#print axioms QueenDom.enumCases_48_24
#print axioms QueenDom.mem_cases48
#print axioms QueenDom.case_split_48
#print axioms QueenDom.twentyfive_le_card_of_cases48_unsat
#print axioms QueenDom.q48c_dominating
#print axioms QueenDom.gamma_48_le_of_q48c
#print axioms QueenDom.gamma_48_eq_25_of_cases48_unsat
-- the encoder package (lean-sat)
#print axioms QueenDomSat.mem_enumCases
#print axioms QueenDomSat.sat_toCNF
#print axioms QueenDomSat.unsat_toCNF
#print axioms QueenDomSat.caseCNF_eq
#print axioms QueenDomSat.sat_caseCNF

-- every declaration of the modules `Queens48.*`, `QueenDomSat.*`, checked mechanically
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut mods : Array Name := #[]
  let mut cnt : Nat := 0
  let mut thms : Nat := 0
  let mut declaredAxioms : Array Name := #[]
  let mut bad : Array Name := #[]
  for (nm, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? nm then
      let modName := env.header.moduleNames[idx.toNat]!
      if (`Queens48).isPrefixOf modName || (`QueenDomSat).isPrefixOf modName then
        unless mods.contains modName do mods := mods.push modName
        cnt := cnt + 1
        if ci matches .thmInfo _ then thms := thms + 1
        if ci matches .axiomInfo _ then declaredAxioms := declaredAxioms.push nm
        let axs ← collectAxioms nm
        if axs.any fun ax => !(ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound) then
          bad := bad.push nm
  let modsSorted := mods.qsort fun a b => a.toString < b.toString
  logInfo m!"modules Queens48.*, QueenDomSat.*: {modsSorted}"
  logInfo m!"declarations of these modules checked: {cnt} ({thms} theorems); declared as axioms: {declaredAxioms.size}; with an axiom outside [propext, Classical.choice, Quot.sound]: {bad.size} {bad}"
