import Mathlib
import Std.Tactic.BVDecide.LRAT.Checker
import Lean.Replay

/-!
Kernel replay of the `n = 48` development.  Run with `lake env lean Replay48.lean` after `lake build`;
the output is saved in `REPLAY48.txt`.

The base environment is `Mathlib` + `Std.Tactic.BVDecide.LRAT.Checker` (they include every external
import of the development).  The constants stored in the `.olean` files (all three parts) of the modules
listed below are sent to the kernel again (`Lean.Kernel.Environment.replay`, the function behind
`leanchecker`; constructors and recursors are compared with the regenerated ones, and compiler
auxiliaries that are `unsafe` / `partial` are skipped).  The script fails if one is rejected, if one is
an axiom, if a main theorem is missing or is not a theorem, or if an axiom other than `propext`,
`Classical.choice`, `Quot.sound` is reachable.  For that
the axioms reachable from the main theorems are collected in the *replayed* environment by a traversal
that does not use `collectAxioms`.  Two negative controls: an ill-typed proof of `False` and a
`rfl` proof of `gamma 48 = 24` must be rejected, and `True.intro : True`, added in the same way, accepted.

Unlike `#print axioms`, this would notice a declaration that was added to an `.olean` with the kernel
check switched off.  It does not re-check Mathlib, Std and Init.
-/

open Lean Elab Command

def projMods : List Name := [
  `QueenDomSat.Encode, `QueenDomSat.Cases, `QueenDomSat.Formula, `QueenDomSat.Lemmas, `QueenDomSat,
  `QueenDom.Defs, `QueenDom.Basic, `QueenDom.Geometry, `QueenDom.Identities, `QueenDom.Consequences,
  `QueenDom.Symmetry, `QueenDom.Cases, `QueenDom.SymmetryCase, `QueenDom.Enum, `QueenDom.Main,
  `Queens48.Framework, `Queens48.Base, `Queens48.Waste, `Queens48.Extra, `Queens48.Sound, `Queens48.Gamma48,
  `Queens48.Cases48Data, `Queens48.Cases48Pieces, `Queens48.Cases48]

/-- the axioms that are allowed -/
def std3 : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

structure WalkResult where
  visited : NameSet := {}
  count : Nat := 0
  axioms : Array Name := #[]
  missing : Array Name := #[]

def walkK (kenv : Kernel.Environment) (roots : Array Name) : WalkResult := Id.run do
  let mut r : WalkResult := {}
  let mut stack : Array Name := roots
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if r.visited.contains c then continue
    r := { r with visited := r.visited.insert c, count := r.count + 1 }
    match kenv.find? c with
    | some (.axiomInfo v)  =>
      r := { r with axioms := r.axioms.push c }
      stack := stack ++ v.type.getUsedConstants
    | some (.defnInfo v)   => stack := stack ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.thmInfo v)    => stack := stack ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.opaqueInfo v) => stack := stack ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | some (.quotInfo v)   => stack := stack ++ v.type.getUsedConstants
    | some (.ctorInfo v)   => stack := (stack ++ v.type.getUsedConstants).push v.induct
    | some (.recInfo v)    =>
      stack := stack ++ v.type.getUsedConstants
      for rule in v.rules do
        stack := stack ++ rule.rhs.getUsedConstants
    | some (.inductInfo v) => stack := stack ++ v.type.getUsedConstants ++ v.ctors.toArray
    | none                 => r := { r with missing := r.missing.push c }
  return r

run_cmd do
  let env ← getEnv
  let base := env.toKernelEnv
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut nThm : Nat := 0
  let mut nAx : Array Name := #[]
  let mut nSkip : Array Name := #[]
  let mut inBase : Array Name := #[]
  for m in projMods do
    let mFile ← findOLean m
    let sFile := OLeanLevel.server.adjustFileName mFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    let parts ← readModuleDataParts #[mFile, sFile, pFile]
    let some part := parts.back? | throwError "no module data"
    let d : ModuleData := part.1
    let mut thms : Nat := 0
    for name in d.constNames, ci in d.constants do
      newConstants := newConstants.insert name ci
      if ci matches .thmInfo _ then thms := thms + 1
      if ci matches .axiomInfo _ then nAx := nAx.push name
      if ci.isUnsafe || ci.isPartial then nSkip := nSkip.push name
      if (base.find? name).isSome then inBase := inBase.push name
    nThm := nThm + thms
    logInfo m!"read {m}: {d.constNames.size} constants ({thms} theorems) from {mFile.fileName} (+ .server, .private)"
  let distinctThms : Nat := newConstants.fold (fun (k : Nat) _ ci => if ci matches .thmInfo _ then k + 1 else k) 0
  unless nAx.isEmpty do throwError m!"declared axioms: {nAx}"
  unless inBase.isEmpty do throwError m!"already in the base environment: {inBase}"
  logInfo m!"to replay: {newConstants.size} distinct constants, {distinctThms} of them theorems; declared axioms among them: {nAx}; unsafe/partial (skipped by replay): {nSkip}; already present in the base environment: {inBase}"
  logInfo m!"base environment contains QueenDom.gamma: {(base.find? `QueenDom.gamma).isSome}, QueenDomSat.caseFormula: {(base.find? `QueenDomSat.caseFormula).isSome}"
  let t0 ← IO.monoMsNow
  let kenv ← base.replay newConstants
  let t1 ← IO.monoMsNow
  logInfo m!"REPLAY OK: the kernel accepted all of them ({t1 - t0} ms)"
  -- controls: `bogus` makes a theorem without any check; only the kernel can reject it
  let bogus (nm : Name) (type value : Expr) : ConstantInfo :=
    .thmInfo { name := nm, levelParams := [], type := type, value := value, all := [nm] }
  let _ ← kenv.replay (({} : Std.HashMap Name ConstantInfo).insert `Replay48.good
    (bogus `Replay48.good (mkConst ``True) (mkConst ``True.intro)))
  logInfo m!"positive control: accepted: True.intro : True (added by the same function)"
  for (what, nm, type, value) in
      [("ill-typed proof of False", `Replay48.bogus1, mkConst ``False, mkConst ``True.intro),
       ("proof of gamma 48 = 24 by rfl", `Replay48.bogus2,
        mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkApp (mkConst `QueenDom.gamma) (mkRawNatLit 48)) (mkRawNatLit 24),
        mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkRawNatLit 24))] do
    let ok ← try
        let _ ← kenv.replay (({} : Std.HashMap Name ConstantInfo).insert nm (bogus nm type value))
        pure true
      catch e => do logInfo m!"  (message: {← (e.toMessageData.toString)})"; pure false
    if ok then throwError m!"NEGATIVE CONTROL FAILED: accepted: {what}"
    logInfo m!"negative control: rejected: {what}"
  let mains : Array Name := #[`QueenDom.gamma_48_eq_25_of_formulas_unsat,
    `QueenDom.igamma_48_eq_25_of_formulas_unsat, `QueenDom.gamma_48_eq_25_of_lrat_check,
    `QueenDom.Sat.lt_gamma_of_formulas_unsat, `QueenDom.Sat.caseFormula_sat_of_caseSat,
    `QueenDom.gamma_48_le, `QueenDom.igamma_48_le, `QueenDom.q48c_dominating,
    `QueenDom.q48i_dominating, `QueenDom.q48i_independent,
    `QueenDomSat.mem_enumCases, `QueenDom.Sat.enumCases_map_toT,
    `QueenDom.enumCases_48_24, `QueenDom.cases48_length, `QueenDom.gamma_48_eq_25_of_cases48_unsat]
  for c in mains do
    let kind := match kenv.find? c with
      | some (.thmInfo _) => "theorem" | some (.axiomInfo _) => "AXIOM" | some _ => "other" | none => "MISSING"
    let r := walkK kenv #[c]
    unless kind == "theorem" do throwError m!"{c}: {kind}"
    unless r.missing.isEmpty do throwError m!"{c}: missing {r.missing}"
    unless r.axioms.all std3.contains do throwError m!"{c}: axioms {r.axioms}"
    logInfo m!"in the replayed environment: {c} [{kind}] -> {r.count} constants in its closure; axioms: {r.axioms}; missing: {r.missing}"
  let rAll := walkK kenv (newConstants.toList.map (·.1)).toArray
  unless rAll.axioms.all std3.contains do throwError m!"axioms {rAll.axioms}"
  unless rAll.missing.all nSkip.contains do throwError m!"missing {rAll.missing}"
  logInfo m!"closure of ALL replayed constants: {rAll.count} constants; axioms: {rAll.axioms}; missing: {rAll.missing}"
  logInfo m!"ALL CHECKS PASSED"
