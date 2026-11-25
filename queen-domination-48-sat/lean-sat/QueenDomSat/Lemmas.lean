/-
First lemmas about the encoder: the semantics of `toCNF` / `caseCNF` in terms of DIMACS literals, and the
decomposition of the clause lists into their groups.  (No Mathlib.)
-/
module

public import QueenDomSat.Encode
public import Std.Sat.CNF.Sat

@[expose] public section

namespace QueenDomSat

open Std.Sat

/-- The DIMACS literal `l` is true under the assignment `a` of the atoms (atom `v - 1` for the
variable `v`): `a (|l| - 1) = true` for `l > 0`, `a (|l| - 1) = false` for `l < 0`. -/
def LitTrue (a : Nat → Bool) (l : Int) : Prop := a (l.natAbs - 1) = decide (0 < l)

instance (a : Nat → Bool) (l : Int) : Decidable (LitTrue a l) := by unfold LitTrue; infer_instance

/-- Some literal of the clause is true under `a`. -/
def ClauseTrue (a : Nat → Bool) (c : Clause) : Prop := ∃ l ∈ c, LitTrue a l

theorem litTrue_ofNat {a : Nat → Bool} {v : Nat} (hv : 0 < v) : LitTrue a (v : Int) ↔ a (v - 1) = true := by
  simp [LitTrue, hv]

theorem litTrue_neg_ofNat {a : Nat → Bool} {v : Nat} (hv : 0 < v) :
    LitTrue a (-(v : Int)) ↔ a (v - 1) = false := by
  have h : ¬ (v : Int) < 0 := by omega
  simp [LitTrue, h]

/-! ### `toCNF` -/

theorem literals_clauseToStd (c : Clause) : (clauseToStd c).literals = c.map litToStd := by
  simp [clauseToStd]

theorem sat_clauseToStd {a : Nat → Bool} {c : Clause} :
    CNF.Clause.Sat a (clauseToStd c) ↔ ClauseTrue a c := by
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  simp only [← CNF.Clause.mem_literals_iff, literals_clauseToStd, List.mem_map, ClauseTrue, LitTrue]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, h⟩
    exact ⟨l, hl, h⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨_, ⟨l, hl, rfl⟩, h⟩

theorem size_toCNF (cls : Array Clause) : (toCNF cls).clauses.size = cls.size := by
  simp [toCNF]

/-- The clause with the LRAT identifier `i + 1` is the `i`-th clause of the array. -/
theorem getElem_toCNF (cls : Array Clause) (i : Nat) (h : i < cls.size) :
    (toCNF cls).clauses[i]'(by simpa [toCNF] using h) = clauseToStd cls[i] := by
  simp [toCNF]

theorem sat_toCNF {a : Nat → Bool} {cls : Array Clause} :
    CNF.Sat a (toCNF cls) ↔ ∀ c ∈ cls, ClauseTrue a c := by
  rw [CNF.sat_iff_all_mem_sat]
  simp only [CNF.Internal.mem_iff, toCNF, Array.mem_map]
  constructor
  · intro h c hc
    exact sat_clauseToStd.mp (h _ ⟨c, hc, rfl⟩)
  · rintro h _ ⟨c, hc, rfl⟩
    exact sat_clauseToStd.mpr (h c hc)

theorem toCNF_append (A B : Array Clause) : toCNF (A ++ B) = toCNF A ++ toCNF B := by
  rw [CNF.Internal.ext_iff, CNF.Internal.clauses_append]
  simp [toCNF]

/-- The formula of a case is the (shared) base formula followed by the frame-dependent clauses. -/
theorem caseCNF_eq (B : Base) (ml mr mb mt : Nat) :
    caseCNF B ml mr mb mt = toCNF B.cls ++ toCNF (caseExtra B ml mr mb mt).1 := by
  rw [caseCNF, toCNF_append]

/-- `toCNF cls` is unsatisfiable iff no assignment makes every clause of `cls` true. -/
theorem unsat_toCNF {cls : Array Clause} :
    CNF.Unsat (toCNF cls) ↔ ∀ a : Nat → Bool, ¬ ∀ c ∈ cls, ClauseTrue a c := by
  rw [CNF.unsat_iff_not_sat]
  simp only [sat_toCNF]

/-! ### The clause groups -/

theorem mem_baseClauses {n k dR dC dT dS : Nat} {c : Clause} :
    c ∈ baseClauses n k dR dC dT dS ↔
      c ∈ defCls n ∨ c ∈ domCls n ∨ c ∈ cardCls n k dR dC dT dS ∨ c ∈ amoCls n dR dC dT dS ∨
        c ∈ queensCls n k dR dC dT dS := by
  simp only [baseClauses, List.mem_append]

theorem mem_cls_mkBase {n k dR dC dT dS : Nat} {c : Clause} :
    c ∈ (mkBase n k dR dC dT dS).cls ↔ c ∈ baseClauses n k dR dC dT dS := by
  simp [mkBase]

/-- The clauses of `extraGroup`: FRAME, (F) started at `nv`, (V) started where (F) stopped, (H)
started where (V) stopped. -/
theorem mem_cls_extraGroup {n k dR dC dT dS a b c d nv : Nat} {cl : Clause} :
    cl ∈ (extraGroup n k dR dC dT dS a b c d nv).cls ↔
      cl ∈ frameCls n a b c d ∨ cl ∈ (groupF n k dR dC dT dS a b c d nv).cls ∨
      cl ∈ (groupV n k dR dT dS a b c d (nv + (groupF n k dR dC dT dS a b c d nv).new)).cls ∨
      cl ∈ (groupH n k dC dT dS a b c d (nv + (groupF n k dR dC dT dS a b c d nv).new +
        (groupV n k dR dT dS a b c d (nv + (groupF n k dR dC dT dS a b c d nv).new)).new)).cls := by
  simp only [extraGroup, List.mem_append]

theorem mem_caseExtra {B : Base} {ml mr mb mt : Nat} {cl : Clause} :
    cl ∈ (caseExtra B ml mr mb mt).1 ↔
      cl ∈ (extraGroup B.n B.k B.dR B.dC B.dT B.dS ml (B.n - 1 - mr) mb (B.n - 1 - mt) B.nv).cls := by
  simp [caseExtra]

/-- An assignment satisfies the formula of a case iff it makes every clause of the base formula and
every frame-dependent clause true. -/
theorem sat_caseCNF {a : Nat → Bool} {B : Base} {ml mr mb mt : Nat} :
    CNF.Sat a (caseCNF B ml mr mb mt) ↔
      (∀ c ∈ B.cls, ClauseTrue a c) ∧
      (∀ c ∈ (extraGroup B.n B.k B.dR B.dC B.dT B.dS ml (B.n - 1 - mr) mb (B.n - 1 - mt) B.nv).cls,
        ClauseTrue a c) := by
  simp only [caseCNF, sat_toCNF, Array.mem_append, mem_caseExtra]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    · exact h1 c hc
    · exact h2 c hc

/-! ### Cardinality constraints -/

theorem atmostCls_of_neg {lits : List Int} {k : Int} {nv : Nat} (h : k < 0) :
    atmostCls lits k nv = [[]] := by
  simp [atmostCls, h]

theorem atmostCls_of_le {lits : List Int} {k : Int} {nv : Nat} (h0 : 0 ≤ k) (h : (lits.length : Int) ≤ k) :
    atmostCls lits k nv = [] := by
  have h2 : ¬ k < 0 := by omega
  simp [atmostCls, h2, h]

theorem atmostCls_zero {lits : List Int} {nv : Nat} (h : lits ≠ []) :
    atmostCls lits 0 nv = lits.map fun l => [-l] := by
  have h3 : ¬ lits.length = 0 := by simpa using h
  simp [atmostCls, h3]

/-- The main branch of `atmost`: the sequential counter with `k` counter variables per row. -/
theorem atmostCls_main {lits : List Int} {k : Int} {nv : Nat} (h0 : 0 < k) (h1 : k < (lits.length : Int)) :
    atmostCls lits k nv = atmostSeq lits k.toNat nv := by
  have h2 : ¬ k < 0 := by omega
  have h3 : ¬ (lits.length : Int) ≤ k := by omega
  have h4 : ¬ k = 0 := by omega
  simp [atmostCls, h2, h3, h4]

theorem atmostNew_main {len : Nat} {k : Int} (h0 : 0 < k) (h1 : k < (len : Int)) :
    atmostNew len k = (len - 1) * k.toNat := by
  simp [atmostNew, h0, h1]

theorem atmostNew_of_not {len : Nat} {k : Int} (h : ¬ (0 < k ∧ k < (len : Int))) : atmostNew len k = 0 := by
  simp [atmostNew, h]

/-- The clauses of the sequential counter, literal by literal. -/
theorem mem_atmostSeq {lits : List Int} {k nv : Nat} {c : Clause} :
    c ∈ atmostSeq lits k nv ↔ ∃ (i : Nat) (l : Int), lits[i]? = some l ∧ c ∈ atmostRow nv k lits.length l i := by
  simp only [atmostSeq, atmostRows, List.mem_flatMap, Prod.exists, List.mk_mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨l, i, h1, h2⟩
    exact ⟨i, l, h1, h2⟩
  · rintro ⟨i, l, h1, h2⟩
    exact ⟨l, i, h1, h2⟩

/-! ### `waste` -/

theorem wasteLines_nil (full : Bool) (nv : Nat) :
    wasteLines full [] nv = { cls := [], lits := [], new := 0 } := rfl

theorem wasteLines_cons (full : Bool) (L : WLine) (Ls : List WLine) (nv : Nat) :
    wasteLines full (L :: Ls) nv =
      { cls := wasteLineCls L nv ++ (wasteLines full Ls (nv + L.nls.length)).cls
        lits := wasteLineLits full L nv ++ (wasteLines full Ls (nv + L.nls.length)).lits
        new := L.nls.length + (wasteLines full Ls (nv + L.nls.length)).new } := rfl

/-- The loop over the lines allocates one variable `e` per non-corner incidence. -/
theorem wasteLines_new (full : Bool) (Ls : List WLine) (nv : Nat) :
    (wasteLines full Ls nv).new = (Ls.map fun L => L.nls.length).sum := by
  induction Ls generalizing nv with
  | nil => rfl
  | cons L Ls ih => simp [wasteLines_cons, ih]

/-- The clauses `[-lv(L), -nl, e]` of one line: the `j`-th non-`None` literal `nl` defines the variable
`e = nv + j + 1`. -/
theorem mem_wasteLineCls {L : WLine} {nv : Nat} {c : Clause} :
    c ∈ wasteLineCls L nv ↔ ∃ (j : Nat) (v : Nat), L.nls[j]? = some v ∧
      c = [-(L.lv : Int), -(v : Int), ((nv + j + 1 : Nat) : Int)] := by
  simp only [wasteLineCls, List.mem_map, Prod.exists, List.mk_mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨v, j, h, rfl⟩
    exact ⟨j, v, h, rfl⟩
  · rintro ⟨j, v, h, rfl⟩
    exact ⟨v, j, h, rfl⟩

theorem length_wasteLineLits (full : Bool) (L : WLine) (nv : Nat) :
    (wasteLineLits full L nv).length = lineCopies full L.onLen + L.nls.length := by
  simp [wasteLineLits]

/-- `waste` allocates the variables `e` of the lines, then one variable `f` per square. -/
theorem waste_new (n a b c d : Nat) (full : Bool) (sqs : List (Nat × Nat)) (nv : Nat) :
    (waste n a b c d full sqs nv).new =
      ((wasteLineList n a b c d sqs).map fun L => L.nls.length).sum + sqs.length := by
  simp [waste, wasteLines_new]

/-- The squares of a set on a difference diagonal. -/
theorem mem_onT {n a b : Nat} {sqs : List (Nat × Nat)} {i : Nat} {sq : Nat × Nat} :
    sq ∈ onT n a b sqs i ↔
      a ≤ sq.1 ∧ sq.1 ≤ b ∧ n - 1 ≤ sq.1 + i ∧ sq.2 = sq.1 + i - (n - 1) ∧ sq ∈ sqs := by
  obtain ⟨x, y⟩ := sq
  simp only [onT, List.mem_map, List.mem_filter, List.mem_range', decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨x', ⟨⟨j, hj, rfl⟩, h1, h2⟩, rfl, rfl⟩
    exact ⟨by omega, by omega, h1, rfl, h2⟩
  · rintro ⟨h1, h2, h3, rfl, h5⟩
    exact ⟨x, ⟨⟨x - a, by omega, by omega⟩, h3, h5⟩, rfl, rfl⟩

/-- The squares of a set on a sum diagonal. -/
theorem mem_onS {a b : Nat} {sqs : List (Nat × Nat)} {s : Nat} {sq : Nat × Nat} :
    sq ∈ onS a b sqs s ↔ a ≤ sq.1 ∧ sq.1 ≤ b ∧ sq.1 + sq.2 = s ∧ sq ∈ sqs := by
  obtain ⟨x, y⟩ := sq
  simp only [onS, List.mem_map, List.mem_filter, List.mem_range', decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨x', ⟨⟨j, hj, rfl⟩, h1, h2⟩, rfl, rfl⟩
    exact ⟨by omega, by omega, by omega, h2⟩
  · rintro ⟨h1, h2, rfl, h5⟩
    exact ⟨x, ⟨⟨x - a, by omega, by omega⟩, by omega, by simpa using h5⟩, rfl, by omega⟩

/-- The border squares. -/
theorem mem_borderSqs {a b c d : Nat} {sq : Nat × Nat} :
    sq ∈ borderSqs a b c d ↔
      (a ≤ sq.1 ∧ sq.1 ≤ b ∧ c ≤ sq.2 ∧ sq.2 ≤ d) ∧ (sq.1 = a ∨ sq.1 = b ∨ sq.2 = c ∨ sq.2 = d) := by
  obtain ⟨x, y⟩ := sq
  simp only [borderSqs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range',
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨x', ⟨j, hj, rfl⟩, y', ⟨⟨j', hj', rfl⟩, h⟩, rfl, rfl⟩
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, h⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, h⟩
    exact ⟨x, ⟨x - a, by omega, by omega⟩, y, ⟨⟨y - c, by omega, by omega⟩, h⟩, rfl, rfl⟩

/-- The squares of the vertical sides. -/
theorem mem_vsideSqs {a b c d : Nat} {sq : Nat × Nat} :
    sq ∈ vsideSqs a b c d ↔ (c ≤ sq.2 ∧ sq.2 ≤ d) ∧ (sq.1 = a ∨ sq.1 = b) := by
  obtain ⟨x, y⟩ := sq
  simp only [vsideSqs, List.mem_flatMap, List.mem_map, List.mem_range', List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq]
  constructor
  · rintro ⟨x', hx, y', ⟨j, hj, rfl⟩, rfl, rfl⟩
    exact ⟨⟨by omega, by omega⟩, hx⟩
  · rintro ⟨⟨h1, h2⟩, h⟩
    exact ⟨x, h, y, ⟨y - c, by omega, by omega⟩, rfl, rfl⟩

/-- The squares of the horizontal sides. -/
theorem mem_hsideSqs {a b c d : Nat} {sq : Nat × Nat} :
    sq ∈ hsideSqs a b c d ↔ (a ≤ sq.1 ∧ sq.1 ≤ b) ∧ (sq.2 = c ∨ sq.2 = d) := by
  obtain ⟨x, y⟩ := sq
  simp only [hsideSqs, List.mem_flatMap, List.mem_map, List.mem_range', List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq]
  constructor
  · rintro ⟨y', hy, x', ⟨j, hj, rfl⟩, rfl, rfl⟩
    exact ⟨⟨by omega, by omega⟩, hy⟩
  · rintro ⟨⟨h1, h2⟩, h⟩
    exact ⟨y, h, x, ⟨x - a, by omega, by omega⟩, rfl, rfl⟩

end QueenDomSat
