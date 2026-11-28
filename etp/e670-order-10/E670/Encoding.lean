import Std.Sat.CNF
import E670.Normal

/-!
# The propositional formula

The variable `var x y z` says `x ◇ y = z`.  `formula` lists clauses that hold in every ten-element
model in normal form; `sat_formula` proves this.  The clauses say that

* every cell has exactly one value,
* every row takes every value exactly once,
* the law holds, in its three directions (`law_entry`, `law_entry_cancel`, `law_entry_cancel₂`),
* `0 ◇ y ≤ y + 1`,
* if `0 ◇ 0 = 0` then every element is idempotent.
-/

namespace E670

open Std.Sat

abbrev Lit := Literal Nat
abbrev Cl := List Lit

def var (x y z : Fin 10) : Nat := 100 * x.val + 10 * y.val + z.val
def pos (x y z : Fin 10) : Lit := (var x y z, true)
def neg (x y z : Fin 10) : Lit := (var x y z, false)

/-- The assignment read off from a table. -/
def assign (op : Op) (i : Nat) : Bool :=
  decide ((op (Fin.ofNat 10 (i / 100)) (Fin.ofNat 10 (i / 10))).val = i % 10)

theorem assign_var (op : Op) (x y z : Fin 10) : assign op (var x y z) = decide (op x y = z) := by
  obtain ⟨hx, hy, hz⟩ : Fin.ofNat 10 (var x y z / 100) = x ∧ Fin.ofNat 10 (var x y z / 10) = y ∧
      var x y z % 10 = z.val := by
    simp only [Fin.ext_iff, var, Fin.val_ofNat]; omega
  simp only [assign, hx, hy, hz, Fin.val_inj]

/-- A clause is satisfied when one of its literals is. -/
def csat (α : Nat → Bool) (c : Cl) : Bool := c.any fun l => α l.1 == l.2

/-! A clause read as a statement about the table: its negative literals are hypotheses. -/

theorem csat_neg {op : Op} {x y z : Fin 10} {c : Cl} :
    csat (assign op) (neg x y z :: c) = true ↔ (op x y = z → csat (assign op) c = true) := by
  by_cases h : op x y = z <;> simp [csat, neg, assign_var, h]

theorem csat_pos {op : Op} {x y z : Fin 10} {c : Cl} :
    csat (assign op) (pos x y z :: c) = true ↔ (op x y = z ∨ csat (assign op) c = true) := by
  simp [csat, pos, assign_var]

theorem csat_nil {α : Nat → Bool} : csat α [] = true ↔ False := by
  simp [csat]

/-- A clause containing the literal `x ◇ y = z` for the actual value `z` is satisfied. -/
theorem csat_of_mem {op : Op} {x y : Fin 10} {c : Cl} (h : pos x y (op x y) ∈ c) :
    csat (assign op) c = true :=
  List.any_eq_true.mpr ⟨_, h, by simp [pos, assign_var]⟩

def R : List (Fin 10) := List.finRange 10

/-- Every cell has exactly one value. -/
def cellClauses : List Cl :=
  R.flatMap fun x => R.flatMap fun y =>
    (R.map fun z => pos x y z) ::
      R.flatMap fun z₁ => (R.filter (z₁ < ·)).map fun z₂ => [neg x y z₁, neg x y z₂]

/-- Every value occurs exactly once in every row. -/
def rowClauses : List Cl :=
  R.flatMap fun x => R.flatMap fun z =>
    (R.map fun y => pos x y z) ::
      R.flatMap fun y₁ => (R.filter (y₁ < ·)).map fun y₂ => [neg x y₁ z, neg x y₂ z]

/-- With `a = x ◇ y`, `b = a ◇ y` and `c = x ◇ b` the law says `y ◇ c = x`. -/
def lawClauses : List Cl :=
  R.flatMap fun x => R.flatMap fun y => R.flatMap fun a => R.flatMap fun b => R.flatMap fun c =>
    [[neg x y a, neg a y b, neg x b c, pos y c x],
     [neg x y a, neg a y b, neg y c x, pos x b c],
     [neg x y a, neg x b c, neg y c x, pos a y b]]

/-- `0 ◇ y ≤ y + 1`. -/
def chainUnits : List Cl :=
  R.flatMap fun y => (R.filter (y.val + 1 < ·.val)).map fun z => [neg 0 y z]

/-- If `0 ◇ 0 = 0` then every element is idempotent. -/
def sideClauses : List Cl := R.map fun x => [neg 0 0 0, pos x x x]

/-- Clauses that hold in every ten-element model in normal form. -/
def formula : List Cl :=
  cellClauses ++ rowClauses ++ lawClauses ++ chainUnits ++ sideClauses

theorem sat_cellClauses (op : Op) : ∀ c ∈ cellClauses, csat (assign op) c = true := by
  intro cl hc
  simp only [cellClauses, R, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_cons,
    List.mem_finRange, decide_eq_true_eq, true_and] at hc
  obtain ⟨x, y, rfl | ⟨z₁, z₂, hlt, rfl⟩⟩ := hc
  · exact csat_of_mem (List.mem_map_of_mem (List.mem_finRange (op x y)))
  · simp only [csat_neg, csat_nil]
    exact fun h₁ h₂ => Fin.ne_of_lt hlt (h₁.symm.trans h₂)

/-- The row clauses hold in a table whose rows are permutations. -/
theorem sat_rowClauses {op : Op} (surj : ∀ x z, ∃ y, op x y = z)
    (inj : ∀ {x a b}, op x a = op x b → a = b) : ∀ c ∈ rowClauses, csat (assign op) c = true := by
  intro cl hc
  simp only [rowClauses, R, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_cons,
    List.mem_finRange, decide_eq_true_eq, true_and] at hc
  obtain ⟨x, z, rfl | ⟨y₁, y₂, hlt, rfl⟩⟩ := hc
  · obtain ⟨y, rfl⟩ := surj x z
    exact csat_of_mem (List.mem_map_of_mem (List.mem_finRange y))
  · simp only [csat_neg, csat_nil]
    exact fun h₁ h₂ => Fin.ne_of_lt hlt (inj (h₁.trans h₂.symm))

theorem sat_chainUnits {op : Op} (chain : ChainRow op) :
    ∀ c ∈ chainUnits, csat (assign op) c = true := by
  intro cl hc
  simp only [chainUnits, R, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, decide_eq_true_eq, true_and] at hc
  obtain ⟨y, z, hlt, rfl⟩ := hc
  simp only [csat_neg, csat_nil]
  rintro rfl
  exact Nat.not_le_of_gt hlt (chain y)

theorem sat_sideClauses {op : Op} (side : op 0 0 = 0 → ∀ x, op x x = x) :
    ∀ c ∈ sideClauses, csat (assign op) c = true := by
  intro cl hc
  simp only [sideClauses, R, List.mem_map, List.mem_finRange, true_and] at hc
  obtain ⟨x, rfl⟩ := hc
  simp only [csat_neg, csat_pos, csat_nil, or_false]
  exact fun h0 => side h0 x

theorem sat_formula {op : Op} (law : Law op) (chain : ChainRow op)
    (side : op 0 0 = 0 → ∀ x, op x x = x) : ∀ c ∈ formula, csat (assign op) c = true := by
  intro cl hc
  simp only [formula, List.mem_append] at hc
  rcases hc with (((hc | hc) | hc) | hc) | hc
  · exact sat_cellClauses op cl hc
  · exact sat_rowClauses (left_surjective law) (left_injective law) cl hc
  · -- the law
    simp only [lawClauses, R, List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
      List.mem_finRange, true_and, or_false] at hc
    obtain ⟨x, y, a, b, c, rfl | rfl | rfl⟩ := hc <;>
      simp only [csat_neg, csat_pos, csat_nil, or_false]
    · exact law_entry law
    · exact law_entry_cancel law
    · exact law_entry_cancel₂ law
  · exact sat_chainUnits chain cl hc
  · exact sat_sideClauses side cl hc

/-- The formula with the given clauses, in the form the certificate checker takes. -/
def toCNF (l : List Cl) : CNF Nat := ⟨(l.map CNF.Clause.ofLiterals).toArray⟩

theorem sat_toCNF {α : Nat → Bool} {l : List Cl} (h : ∀ c ∈ l, csat α c = true) :
    CNF.Sat α (toCNF l) := by
  refine CNF.sat_of_all_mem_sat fun c (hc : c ∈ (l.map CNF.Clause.ofLiterals).toArray) => ?_
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hc)
  -- both sides say that `c'` contains a literal that `α` makes true
  simpa [CNF.Clause.sat_iff_exists_mem_eq, ← CNF.Clause.mem_literals_iff, csat] using h c' hc'

end E670
