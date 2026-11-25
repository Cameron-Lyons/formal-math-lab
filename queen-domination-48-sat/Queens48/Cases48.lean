/-
The case list for `n = 48`, `k = 24`: the 47,580 cases of the run records (`data/frame/d_48_24.jsonl.xz`,
written by `code/frame/run_cases48.py 48 24`) coincide with the case list `L(48, 24)`; the comparison is a
kernel computation (`decide +kernel`, no `native_decide`, one computation per pair of horizontal margins,
see `Cases48Pieces.lean`).
Final theorems for `n = 48` (instances of the generic statements of `Main.lean`), and the upper bound
`γ(Q_48) ≤ 25` from the explicit set of `data/frame/q48_25.json`.
-/
module

public import Queens48.Cases48Pieces

@[expose] public section

namespace QueenDom

/-- The case codes of the `n = 48`, `k = 24` run (`Queens48/Cases48Data.lean`), in lexicographic
order. -/
def caseCodes48 : List ℕ := tableList 24 caseCodes48T

/-- The cases of the `n = 48`, `k = 24` run (`data/frame/d_48_24.jsonl.xz`), sorted. -/
def cases48 : List Case := caseCodes48.map Case.ofCode

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The run records contain 47,580 cases. -/
theorem cases48_length : cases48.length = 47580 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- There are 14,365 canonical frames for `n = 48`, `k = 24`. -/
theorem enumFrames_48_24_length : (enumFrames 48 24).length = 14365 := by decide +kernel

/-- **The case list of the run is the case list `L(48, 24)`** (kernel computation, assembled from one
computation per pair of horizontal margins in `Cases48Pieces.lean`). -/
theorem enumCases_48_24 : enumCases 48 24 = cases48 := enumCases_48_24_table

/-- A case is in the run records iff its frame is canonical and it is admissible for `(48, 24)`. -/
theorem mem_cases48 {cs : Case} : cs ∈ cases48 ↔ CanonAdm 48 24 cs :=
  mem_of_enumCases_eq enumCases_48_24

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The codes of the 14,365 canonical frames are strictly increasing (kernel computation). -/
theorem enumFrames_48_24_chain : ((enumFrames 48 24).map frameCode).IsChain (· < ·) := by
  decide +kernel

/-- The 14,365 canonical frames are pairwise distinct. -/
theorem enumFrames_48_24_nodup : (enumFrames 48 24).Nodup :=
  nodup_of_frameCode_chain enumFrames_48_24_chain

/-- The frames occurring in the run records are exactly the canonical frames for `(48, 24)`. -/
theorem frames_cases48 : (cases48.map Case.frame).toFinset = (enumFrames 48 24).toFinset :=
  frames_of_enumCases_eq enumCases_48_24 (by norm_num) (by norm_num)

/-- The run records contain exactly 14,365 distinct frames. -/
theorem card_frames_cases48 : (cases48.map Case.frame).toFinset.card = 14365 := by
  rw [card_frames_of_enumCases_eq enumCases_48_24 (by norm_num) (by norm_num) enumFrames_48_24_chain,
    enumFrames_48_24_length]

/-- **Case split for `n = 48`.**  Every dominating set of 24 queens on the `48 × 48` board has a
symmetric image satisfying all constraints of one of the 47,580 cases of the run. -/
theorem case_split_48 (D : Finset (Sq 48)) (hD : Dominating D) (hc : D.card = 24) :
    ∃ g : Sym, ∃ cs ∈ cases48, CaseSat 48 24 cs (g.image D) :=
  case_split_of_enumCases_eq enumCases_48_24 (by norm_num) D hD hc

/-- **The run covers every admissible case up to symmetry**: every admissible
(frame, deficit vector) for `(48, 24)` has an image under one of the eight symmetries (acting on cases
by the table `geom.case_images`) in the list of the 47,580 cases of the run. -/
theorem cases48_cover (cs : Case) (h : Admissible 48 24 cs) : ∃ g : Sym, g.actCase cs ∈ cases48 :=
  cover_of_enumCases_eq enumCases_48_24 cs h

/-- **`γ(Q_48) ≥ 25`, modulo the SAT certificates.**  If each of the 47,580 cases of the run is
unsatisfiable (this is what the DRAT/LRAT certificates establish, via the CNF encoding of `CaseSat`), then
every dominating set of `Q_48` has at least 25 queens. -/
theorem twentyfive_le_card_of_cases48_unsat
    (H : ∀ cs ∈ cases48, ¬ ∃ D : Finset (Sq 48), CaseSat 48 24 cs D) :
    ∀ D : Finset (Sq 48), Dominating D → 25 ≤ D.card :=
  card_lt_of_enumCases_eq enumCases_48_24 (by norm_num) H

/-- The same statement in terms of the domination number. -/
theorem twentyfive_le_gamma_48_of_cases48_unsat
    (H : ∀ cs ∈ cases48, ¬ ∃ D : Finset (Sq 48), CaseSat 48 24 cs D) : 25 ≤ gamma 48 :=
  lt_gamma_of_enumCases_eq enumCases_48_24 (by norm_num) H

/-! ### Upper bound: 25 queens dominate `Q_48`

The set is the one of `data/frame/q48_25.json`.  (`Queens48/Gamma48.lean` uses another set, whose queens
are also pairwise non-attacking.) -/

/-- The dominating set of 25 queens of `data/frame/q48_25.json` (squares `(column, row)`). -/
def q48c : Finset (Sq 48) :=
  {(1, 31), (3, 17), (5, 39), (7, 43), (8, 8), (9, 3), (11, 29), (13, 35), (15, 9), (17, 15),
   (19, 45), (21, 25), (23, 19), (25, 23), (27, 1), (29, 7), (31, 37), (33, 5), (35, 21), (37, 47),
   (39, 41), (41, 11), (43, 33), (45, 27), (47, 13)}

set_option maxRecDepth 100000 in
theorem q48c_card : q48c.card = 25 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The 25 queens dominate `Q_48` (kernel computation over the 2304 squares). -/
theorem q48c_dominating : Dominating q48c := by decide +kernel

/-- `γ(Q_48) ≤ 25` (unconditional), from the set `q48c`. -/
theorem gamma_48_le_of_q48c : gamma 48 ≤ 25 := q48c_card ▸ gamma_le q48c_dominating

/-- **`γ(Q_48) = 25`, modulo the SAT certificates.**  (The upper bound is unconditional; the hypothesis is
used only for the lower bound.) -/
theorem gamma_48_eq_25_of_cases48_unsat
    (H : ∀ cs ∈ cases48, ¬ ∃ D : Finset (Sq 48), CaseSat 48 24 cs D) : gamma 48 = 25 :=
  gamma_eq_of_lt_of_dominating (twentyfive_le_gamma_48_of_cases48_unsat H) q48c_dominating q48c_card

end QueenDom
