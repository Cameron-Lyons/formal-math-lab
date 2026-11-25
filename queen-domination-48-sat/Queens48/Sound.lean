/-
Soundness of the CNF encoding (Layer 2), final statements: if `D` satisfies the constraints `CaseSat` of a
case, then the formula `QueenDomSat.caseFormula` of the case (the Lean transcription of the CNF written by
`code/frame/enc.py`) is satisfiable.  Hence: if the formulas of all cases of the case list `L(n, k)` are
unsatisfiable and `k ≤ n - 2`, then `γ(Q_n) > k`.
-/
module

public import Queens48.Extra
public import QueenDom.Main
public import Std.Tactic.BVDecide.LRAT.Checker

@[expose] public section

namespace QueenDom.Sat

open QueenDomSat

variable {n k : ℕ}

/-- A case as the Mathlib-free structure `QueenDomSat.CaseT`, field by field. -/
def toT (cs : QueenDom.Case) : CaseT := ⟨cs.ml, cs.mr, cs.mb, cs.mt, cs.dR, cs.dC, cs.dT, cs.dS⟩

/-- The Mathlib-free case list is the case list `L(n, k)`, in the same order.  (Not used below.) -/
theorem enumCases_map_toT (n k : ℕ) : (QueenDom.enumCases n k).map toT = QueenDomSat.enumCases n k := by
  simp only [QueenDom.enumCases, QueenDomSat.enumCases, QueenDom.casesOfFrame, List.map_flatMap, List.map_map]
  rfl

/-- **Soundness of the CNF encoding.**  If some `D` satisfies the constraints of the case, the formula of the
case is satisfiable. -/
theorem caseFormula_sat_of_caseSat {cs : Case} {D : Finset (Sq n)} (h : CaseSat n k cs D) :
    ∃ a : ℕ → Bool, Std.Sat.CNF.Sat a (caseFormula n k (toT cs)) := by
  obtain ⟨m, hm, hbase⟩ := base_sound h
  obtain ⟨m', hextra⟩ := extra_sound h (baseVars n + m)
  obtain ⟨τ, -, hτ⟩ := hbase.append hextra (boardVal D) fun _ => id
  rw [← hm] at hτ
  refine ⟨fun i => τ (i + 1), sat_toCNF.mpr fun c hc => hτ τ Agree.refl c (List.mem_append.mpr ?_)⟩
  exact (Array.mem_append.mp hc).imp List.mem_toArray.mp List.mem_toArray.mp

/-- **Proposition C with the CNF formulas.**  Let `k ≤ n - 2`.  If the formula of every case of the case list
`L(n, k)` is unsatisfiable, every dominating set of `Q_n` has more than `k` queens. -/
theorem card_lt_of_formulas_unsat (hk : k + 2 ≤ n)
    (H : ∀ cs ∈ QueenDomSat.enumCases n k, (caseFormula n k cs).Unsat) :
    ∀ D : Finset (Sq n), Dominating D → k < D.card := by
  refine no_dominating_of_cases_unsat hk fun cs hcs ⟨D, hD⟩ => ?_
  obtain ⟨a, ha⟩ := caseFormula_sat_of_caseSat hD
  -- `hcs` is also the condition of the Mathlib-free list: the two `CanonAdm` are copies of each other
  exact Std.Sat.CNF.unsat_iff_not_sat.mp (H (toT cs) (QueenDomSat.mem_enumCases.mpr hcs)) a ha

/-- The same in terms of `γ`. -/
theorem lt_gamma_of_formulas_unsat (hk : k + 2 ≤ n)
    (H : ∀ cs ∈ QueenDomSat.enumCases n k, (caseFormula n k cs).Unsat) : k < gamma n :=
  lt_gamma_iff.mpr (card_lt_of_formulas_unsat hk H)

/-- The same with certificates accepted by the LRAT checker of `Std`. -/
theorem lt_gamma_of_lrat_check (hk : k + 2 ≤ n)
    (proofs : CaseT → Array Std.Tactic.BVDecide.LRAT.IntAction)
    (H : ∀ cs ∈ QueenDomSat.enumCases n k,
      Std.Tactic.BVDecide.LRAT.check (proofs cs) (caseFormula n k cs) = true) : k < gamma n :=
  lt_gamma_of_formulas_unsat hk fun cs hcs =>
    Std.Tactic.BVDecide.LRAT.check_sound (proofs cs) (caseFormula n k cs) (H cs hcs)

end QueenDom.Sat
