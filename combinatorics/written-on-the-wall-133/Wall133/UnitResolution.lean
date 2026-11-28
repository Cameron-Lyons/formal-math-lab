module

@[expose] public section

namespace Wall133.UnitResolution

private abbrev Lit := Nat × Bool
abbrev Clause := List (Nat × Bool)

/-- A CNF formula represented as an array of literal-list clauses. -/
structure CNF (α : Type) where
  clauses : Array (List (α × Bool))
deriving DecidableEq

/-- Evaluate a single clause under an assignment. -/
def evalClause {α : Type} (c : List (α × Bool)) (p : α → Bool) : Bool :=
  c.any (fun l => p l.1 == l.2)

/-- Evaluate a CNF formula under an assignment. -/
def CNF.eval {α : Type} (f : CNF α) (p : α → Bool) : Bool :=
  f.clauses.all (fun c => evalClause c p)

/-- A CNF formula is unsatisfiable if every assignment falsifies it. -/
def CNF.Unsat {α : Type} (f : CNF α) : Prop :=
  ∀ p, f.eval p = false

/-- Every literal of c is false under the assignment p. -/
private def Falsified (p : Nat → Bool) (c : Clause) : Prop := ∀ l∈c, p l.1 = !l.2

private def AllValid (p : Nat → Bool) : List Clause → Prop
  | [] => True
  | c :: cs => (¬ Falsified p c) ∧ AllValid p cs

def trace (dead : Clause) : List Clause → Bool
  | [] => false
  | c :: cs =>
    match c.filter (fun l => !(dead.contains l)) with
    | [] => true
    | [l] => trace ((l.1,!l.2) :: dead) cs
    | _ => false

private theorem trace_sound {p : Nat → Bool} {hints : List Clause} {dead : Clause}
    (ht : trace dead hints) (valid : AllValid p hints) (hd : Falsified p dead) : False := by
  induction hints generalizing dead with
  | nil => contradiction
  | cons c cs ih =>
    have vc := valid.1
    have remainder {l : Lit} (hi : l∈c) (hn : l∉dead) :
        l ∈ c.filter (fun t => !(dead.contains t)) := by simpa using And.intro hi hn
    unfold trace at ht
    split at ht
    next h =>
      apply vc
      intro t tt
      by_cases td : t∈dead
      · exact hd _ td
      · have mem := remainder tt td
        rw [h] at mem
        exact False.elim (List.not_mem_nil mem)
    next l h =>
      have live : p l.1 = l.2 := by
        cases hp : p l.1 <;> cases hs : l.2 <;> try rfl
        all_goals exfalso; apply vc; intro t tt
        all_goals by_cases td : t∈dead
        all_goals first | exact hd _ td | skip
        all_goals have mem := remainder tt td
        all_goals rw [h,List.mem_singleton] at mem
        all_goals simp [mem,hp,hs]
      apply ih ht valid.2
      intro t mem
      rcases List.mem_cons.mp mem with h|h
      · subst t; simpa using live
      · exact hd _ h
    next => contradiction

private theorem valid_of_eval {p : Nat → Bool} {c : Clause} (h : evalClause c p = true) :
    ¬Falsified p c := by
  intro falsified
  obtain ⟨l,hl,truth⟩ := List.any_eq_true.mp h
  have he := falsified l hl
  cases l with
  | mk var sign =>
    change (p var == sign) = true at truth
    change p var = !sign at he
    cases sign <;> simp_all

/-- The initial part of the proof database consists of the clauses from the formula;
the remaining lines are consequences of earlier lines. -/
def line (f : CNF Nat) (derived : Array Clause) (i : Nat) : Clause :=
  if h : i < f.clauses.size then f.clauses[i] else derived[i - f.clauses.size]!

/-- Each witness supplies the indices of the clauses used for one derivation. -/
def checkLine (f : CNF Nat) (derived : Array Clause) (i : Nat) (hints : List Nat) : Bool :=
  hints.all (fun j => decide (j < f.clauses.size+i)) &&
    trace derived[i]! (hints.map (line f derived))

private theorem allValid_of_mem {p : Nat → Bool} {cs : List Clause}
    (h : ∀ c∈cs,¬Falsified p c) : AllValid p cs := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    exact ⟨h c (by simp),ih (fun d hd => h d (List.mem_cons_of_mem _ hd))⟩

/-- A valid derivation of the empty clause refutes the original formula. -/
theorem unsat (f : CNF Nat) (derived : Array Clause) (witness : Array (List Nat))
    (verified : ∀ i, i<derived.size → checkLine f derived i witness[i]!)
    (last : Nat) (lastIn : last<derived.size) (empty : derived[last] = []) : f.Unsat := by
  intro p
  cases he : f.eval p with
  | false => rfl
  | true =>
    exfalso
    have good (n : Nat) (hn : n < f.clauses.size + derived.size) : ¬ Falsified p (line f derived n) := by
      induction n using Nat.strongRecOn with
      | ind n earlier =>
        by_cases base : n < f.clauses.size
        · simp only [line,dite_eq_left base]
          exact valid_of_eval (Array.all_eq_true.mp he n base)
        · let i := n - f.clauses.size
          have hi : i < derived.size := by dsimp [i]; omega
          have ni : n = f.clauses.size+i := by dsimp [i]; omega
          have ok := verified i hi
          simp only [checkLine,Bool.and_eq_true_iff] at ok
          simp only [line,dite_eq_right base]
          apply trace_sound ok.2
          apply allValid_of_mem
          intro c hc
          obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
          have prev : j < f.clauses.size+i := of_decide_eq_true (List.all_eq_true.mp ok.1 j hj)
          exact earlier j (by omega) (by omega)
    have g := good (f.clauses.size+last) (by omega)
    simp only [line,show ¬f.clauses.size + last < f.clauses.size by omega,Nat.add_sub_cancel_left] at g
    have eq : derived[last]! = [] := by simpa [getElem!_pos derived last lastIn] using empty
    rw [eq] at g
    exact g (fun _ h => (List.not_mem_nil h).elim)

/-- Combine adjacent ranges of checked lines. -/
theorem join {P : Nat → Prop} {lo cut hi : Nat}
    (left : ∀ i, lo≤i → i<cut → P i) (right : ∀ i, cut≤i → i<hi → P i) :
    ∀ i, lo≤i → i<hi → P i := by
  intro i il ih
  by_cases h : i<cut
  · exact left i il h
  · exact right i (Nat.le_of_not_gt h) ih

theorem rangeChecked (test : Nat → Bool) (lo hi : Nat)
    (valid : (List.range (hi-lo)).all (fun j => test (lo+j))) :
    ∀ i, lo≤i → i<hi → test i := by
  intro i il ih
  have eq : lo+(i-lo)=i := by omega
  simpa only [eq] using List.all_eq_true.mp valid (i-lo) (List.mem_range.mpr (by omega))

end Wall133.UnitResolution
