/-
`γ(Q_48) = i(Q_48) = 25`, given that the formula of every case of the case list `L(48, 24)` is unsatisfiable.

* Upper bound (unconditional): `q48i` is a dominating set of 25 pairwise non-attacking queens;
  kernel computations.
* Lower bound: `QueenDom.Sat.lt_gamma_of_formulas_unsat` for `(n, k) = (48, 24)`.

Östergård and Weakley (Electron. J. Combin. 8 (2001) #R29) proved `i(Q_48), γ(Q_48) ∈ {24, 25}`.
-/
module

public import Queens48.Sound

@[expose] public section

namespace QueenDom

open QueenDom.Sat QueenDomSat

/-! ### The independent domination number -/

variable {n : ℕ} {D : Finset (Sq n)}

/-- `D` is independent: no two squares of `D` attack each other. -/
def Independent (D : Finset (Sq n)) : Prop := ∀ p ∈ D, ∀ q ∈ D, ¬ Attacks p q

/-- Independence is independence in the queen's graph `Q_n`. -/
theorem independent_iff_isIndepSet (D : Finset (Sq n)) :
    Independent D ↔ (queenGraph n).IsIndepSet (D : Set (Sq n)) :=
  ⟨fun h p hp q hq _ => h p hp q hq, fun h _ hp _ hq hpq => h hp hq hpq.1 hpq⟩

/-- The independent domination number `i(Q_n)`: the least size of an independent dominating set. -/
noncomputable def igamma (n : ℕ) : ℕ :=
  sInf {k | ∃ D : Finset (Sq n), Dominating D ∧ Independent D ∧ D.card = k}

theorem igamma_le (hD : Dominating D) (hI : Independent D) : igamma n ≤ D.card :=
  Nat.sInf_le ⟨D, hD, hI, rfl⟩

/-- `γ(Q_n) ≤ i(Q_n)` as soon as some independent dominating set exists. -/
theorem gamma_le_igamma (hD : Dominating D) (hI : Independent D) : gamma n ≤ igamma n := by
  obtain ⟨D', hD', -, hc⟩ : igamma n ∈ {k | ∃ D : Finset (Sq n), Dominating D ∧ Independent D ∧ D.card = k} :=
    Nat.sInf_mem ⟨_, D, hD, hI, rfl⟩
  exact (gamma_le hD').trans hc.le

/-! ### Upper bound -/

/-- An explicit 25-queen independent dominating set of `Q_48` (squares `(column, row)`). -/
def q48i : Finset (Sq 48) :=
  {(1, 31), (3, 9), (5, 19), (7, 29), (9, 35), (11, 45), (13, 3), (15, 23), (17, 11), (19, 1),
   (21, 21), (23, 27), (25, 43), (27, 39), (29, 25), (31, 41), (33, 13), (35, 5), (36, 28), (37, 15),
   (39, 37), (41, 7), (43, 17), (45, 47), (47, 33)}

theorem q48i_card : q48i.card = 25 := by decide +kernel

set_option maxRecDepth 100000 in
theorem q48i_dominating : Dominating q48i := by decide +kernel

set_option maxRecDepth 100000 in
theorem q48i_independent : Independent q48i := by unfold Independent; decide +kernel

/-- `γ(Q_48) ≤ 25` (unconditional). -/
theorem gamma_48_le : gamma 48 ≤ 25 := q48i_card ▸ gamma_le q48i_dominating

/-- `i(Q_48) ≤ 25` (unconditional). -/
theorem igamma_48_le : igamma 48 ≤ 25 := q48i_card ▸ igamma_le q48i_dominating q48i_independent

/-! ### `γ(Q_48) = i(Q_48) = 25` -/

/-- **`γ(Q_48) > 24`, given the unsatisfiability of the 47,580 formulas**: every dominating set of `Q_48` has
at least 25 queens. -/
theorem twentyfive_le_card_of_formulas_unsat
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (caseFormula 48 24 cs).Unsat) :
    ∀ D : Finset (Sq 48), Dominating D → 25 ≤ D.card :=
  card_lt_of_formulas_unsat (by norm_num) H

/-- **`γ(Q_48) = 25`, given the unsatisfiability of the 47,580 formulas.** -/
theorem gamma_48_eq_25_of_formulas_unsat
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (caseFormula 48 24 cs).Unsat) : gamma 48 = 25 :=
  gamma_48_le.antisymm (lt_gamma_of_formulas_unsat (by norm_num) H)

/-- **`i(Q_48) = 25`, given the unsatisfiability of the 47,580 formulas.** -/
theorem igamma_48_eq_25_of_formulas_unsat
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24, (caseFormula 48 24 cs).Unsat) : igamma 48 = 25 :=
  igamma_48_le.antisymm
    (gamma_48_eq_25_of_formulas_unsat H ▸ gamma_le_igamma q48i_dominating q48i_independent)

/-- **`γ(Q_48) = 25`, given a certificate accepted by the LRAT checker of `Std` for every formula.** -/
theorem gamma_48_eq_25_of_lrat_check (proofs : CaseT → Array Std.Tactic.BVDecide.LRAT.IntAction)
    (H : ∀ cs ∈ QueenDomSat.enumCases 48 24,
      Std.Tactic.BVDecide.LRAT.check (proofs cs) (caseFormula 48 24 cs) = true) : gamma 48 = 25 :=
  gamma_48_le.antisymm (lt_gamma_of_lrat_check (by norm_num) proofs H)

end QueenDom
