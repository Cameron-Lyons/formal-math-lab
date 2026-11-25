/-
The case list `L(n, k)` of the frame method as plain data, without Mathlib: a transcription of
`geom.cases_by_frame` (`code/frame/geom.py`).

The definitions `LexLe`, `Canon`, `Admissible`, `CanonAdm`, `FrameOK`, `enumFrames`, `casesOfFrame`,
`enumCases` are copies, symbol for symbol, of the definitions with the same names in
`lean/QueenDom/Symmetry.lean`, `lean/QueenDom/Cases.lean` and `lean/QueenDom/Enum.lean` (with `CaseT` in
place of `QueenDom.Case`), and so are the proofs of `mem_enumFrames` and `mem_enumCases`.
-/
module

@[expose] public section

namespace QueenDomSat

/-- A *case* `(ml, mr, mb, mt; dR, dC, dT, dS)`: the four margins of the frame and the four deficits
(`QueenDom.Case`). -/
structure CaseT where
  ml : Nat
  mr : Nat
  mb : Nat
  mt : Nat
  dR : Nat
  dC : Nat
  dT : Nat
  dS : Nat
deriving DecidableEq, Repr

/-- Lexicographic order on 4-tuples of natural numbers (`QueenDom.LexLe`). -/
def LexLe (a1 a2 a3 a4 b1 b2 b3 b4 : Nat) : Prop :=
  a1 < b1 ∨ a1 = b1 ∧ (a2 < b2 ∨ a2 = b2 ∧ (a3 < b3 ∨ a3 = b3 ∧ a4 ≤ b4))

instance (a1 a2 a3 a4 b1 b2 b3 b4 : Nat) : Decidable (LexLe a1 a2 a3 a4 b1 b2 b3 b4) := by
  unfold LexLe; infer_instance

/-- A frame `(ml, mr, mb, mt) = (p, q, r, s)` is *canonical* if it is lexicographically least among
its eight images (`geom.canonical`, `QueenDom.Canon`); the seven non-trivial images are listed. -/
def Canon (p q r s : Nat) : Prop :=
  LexLe p q r s q p r s ∧ LexLe p q r s p q s r ∧ LexLe p q r s q p s r ∧
  LexLe p q r s r s p q ∧ LexLe p q r s s r p q ∧ LexLe p q r s r s q p ∧ LexLe p q r s s r q p

instance (p q r s : Nat) : Decidable (Canon p q r s) := by unfold Canon; infer_instance

/-- Closed form of canonicity (`QueenDom.canon_iff`). -/
theorem canon_iff (p q r s : Nat) : Canon p q r s ↔ p ≤ q ∧ r ≤ s ∧ (p < r ∨ p = r ∧ q ≤ s) := by
  unfold Canon LexLe; omega

/-- The admissibility conditions of F.2 (`geom.admissible`, `QueenDom.Admissible`), written without
subtraction:
* each deficit is at most `k - 1`;
* `ml + mr ≤ k - dC`, `mb + mt ≤ k - dR`;
* `w = n-1-ml-mr ≥ 1`, `h = n-1-mb-mt ≥ 1`;
* `8k - 4n + 4 - 2(dR+dC+dT+dS) ≥ 0`;
* if `w ≥ h` then `4k - 2n - dT - dS - 2dR + 2[w = h] ≥ 0`;
  if `h ≥ w` then `4k - 2n - dT - dS - 2dC + 2[w = h] ≥ 0`.
(`w ≥ h` iff `ml + mr ≤ mb + mt`.) -/
def Admissible (n k : Nat) (cs : CaseT) : Prop :=
  cs.dR + 1 ≤ k ∧ cs.dC + 1 ≤ k ∧ cs.dT + 1 ≤ k ∧ cs.dS + 1 ≤ k ∧
  cs.ml + cs.mr + cs.dC ≤ k ∧ cs.mb + cs.mt + cs.dR ≤ k ∧
  cs.ml + cs.mr + 2 ≤ n ∧ cs.mb + cs.mt + 2 ≤ n ∧
  4 * n + 2 * (cs.dR + cs.dC + cs.dT + cs.dS) ≤ 8 * k + 4 ∧
  (cs.ml + cs.mr ≤ cs.mb + cs.mt →
    2 * n + cs.dT + cs.dS + 2 * cs.dR ≤ 4 * k + (if cs.ml + cs.mr = cs.mb + cs.mt then 2 else 0)) ∧
  (cs.mb + cs.mt ≤ cs.ml + cs.mr →
    2 * n + cs.dT + cs.dS + 2 * cs.dC ≤ 4 * k + (if cs.ml + cs.mr = cs.mb + cs.mt then 2 else 0))

instance (n k : Nat) (cs : CaseT) : Decidable (Admissible n k cs) := by
  unfold Admissible; infer_instance

/-- A case of the case list `L(n, k)`: canonical frame and admissible (`QueenDom.CanonAdm`). -/
def CanonAdm (n k : Nat) (cs : CaseT) : Prop := Canon cs.ml cs.mr cs.mb cs.mt ∧ Admissible n k cs

instance (n k : Nat) (cs : CaseT) : Decidable (CanonAdm n k cs) := by
  unfold CanonAdm; infer_instance

/-- The conditions on a frame used by `geom.canonical_frames`: canonical, `w ≥ 1`, `h ≥ 1`
(`QueenDom.FrameOK`). -/
def FrameOK (n p q r s : Nat) : Prop := Canon p q r s ∧ p + q + 2 ≤ n ∧ r + s + 2 ≤ n

instance (n p q r s : Nat) : Decidable (FrameOK n p q r s) := by unfold FrameOK; infer_instance

/-- The canonical frames `(ml, mr, mb, mt)` with `ml + mr ≤ k`, `mb + mt ≤ k`, in lexicographic
order (`sorted(geom.canonical_frames(n, k))`, `QueenDom.enumFrames`). -/
def enumFrames (n k : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range (k + 1)).flatMap fun p => (List.range (k + 1 - p)).flatMap fun q =>
  (List.range (k + 1)).flatMap fun r =>
  ((List.range (k + 1 - r)).filter fun s => decide (FrameOK n p q r s)).map fun s => (p, q, r, s)

theorem mem_enumFrames {n k p q r s : Nat} :
    (p, q, r, s) ∈ enumFrames n k ↔ p + q ≤ k ∧ r + s ≤ k ∧ FrameOK n p q r s := by
  simp only [enumFrames, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨p', hp, q', hq, r', hr, s', ⟨hs, hok⟩, rfl, rfl, rfl, rfl⟩
    exact ⟨by omega, by omega, hok⟩
  · rintro ⟨hpq, hrs, hok⟩
    exact ⟨p, by omega, q, by omega, r, by omega, s, ⟨by omega, hok⟩, rfl, rfl, rfl, rfl⟩

/-- The admissible deficit vectors of one frame `f = (ml, mr, mb, mt)`, in lexicographic order
(`QueenDom.casesOfFrame`).  The deficits are enumerated subject to `dR + dC + dT + dS ≤ 4k - 2n + 2`
(the bound `sm` of `geom.cases_by_frame`), which is implied by admissibility. -/
def casesOfFrame (n k : Nat) (f : Nat × Nat × Nat × Nat) : List CaseT :=
  (List.range (4 * k + 3 - 2 * n)).flatMap fun dR =>
  (List.range (4 * k + 3 - 2 * n - dR)).flatMap fun dC =>
  (List.range (4 * k + 3 - 2 * n - dR - dC)).flatMap fun dT =>
  ((List.range (4 * k + 3 - 2 * n - dR - dC - dT)).filter fun dS =>
      decide (Admissible n k ⟨f.1, f.2.1, f.2.2.1, f.2.2.2, dR, dC, dT, dS⟩)).map
    fun dS => ⟨f.1, f.2.1, f.2.2.1, f.2.2.2, dR, dC, dT, dS⟩

/-- The case list `L(n, k)`: every canonical frame with every admissible deficit vector, in
lexicographic order (`geom.cases_by_frame(n, k)`, `QueenDom.enumCases`). -/
def enumCases (n k : Nat) : List CaseT := (enumFrames n k).flatMap (casesOfFrame n k)

/-- The enumeration is exactly the set of cases with canonical frame and admissible
(frame, deficits). -/
theorem mem_enumCases {n k : Nat} {cs : CaseT} : cs ∈ enumCases n k ↔ CanonAdm n k cs := by
  simp only [enumCases, casesOfFrame, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p, q, r, s⟩, hf, dR, -, dC, -, dT, -, dS, ⟨-, hadm⟩, rfl⟩
    exact ⟨(mem_enumFrames.mp hf).2.2.1, hadm⟩
  · rintro ⟨hcan, hadm⟩
    have hadm' := hadm
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := hadm'
    refine ⟨(cs.ml, cs.mr, cs.mb, cs.mt), mem_enumFrames.mpr ⟨by omega, by omega, hcan, h7, h8⟩,
      cs.dR, by omega, cs.dC, by omega, cs.dT, by omega, cs.dS, ⟨by omega, hadm⟩, rfl⟩

/-- The eight integers of a case, in the order of the Python tuples. -/
def CaseT.toList (cs : CaseT) : List Nat := [cs.ml, cs.mr, cs.mb, cs.mt, cs.dR, cs.dC, cs.dT, cs.dS]

/-- The file-name tag `<ml>_<mr>_<mb>_<mt>_<dR>_<dC>_<dT>_<dS>` of a case (`run_cases48.tag_of`). -/
def CaseT.tag (cs : CaseT) : String := "_".intercalate (cs.toList.map fun v => toString v)

end QueenDomSat
