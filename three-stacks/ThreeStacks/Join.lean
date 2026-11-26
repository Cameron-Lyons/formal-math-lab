import ThreeStacks.Replay

namespace ThreeStacks

/-- The three physical stacks, with the top card first in each list. -/
structure Boundary where
  first : List Nat
  second : List Nat
  third : List Nat
  deriving DecidableEq, Repr

/-- Load a prefix into an exact boundary without reading the suffix or producing output. -/
inductive Loads (b : Boundary) : List Nat → List Nat → List Nat → List Nat → Prop where
  | done : Loads b [] b.first b.second b.third
  | input : Loads b i (x :: s) t u → Loads b (x :: i) s t u
  | first : Loads b i s (x :: t) u → Loads b i (x :: s) t u
  | second : Loads b i s t (x :: u) → Loads b i s (x :: t) u

/-- The prefix moves leave the entire unread suffix intact for the continuation. -/
theorem Loads.continue {b : Boundary} {i s t u tail out : List Nat}
    (load : Loads b i s t u) (finish : Run tail b.first b.second b.third out) :
    Run (i ++ tail) s t u out := by
  induction load with
  | done => exact finish
  | input _ ih => exact .input ih
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

/-- A proper cut whose two legal runs agree on every card in all three stacks. -/
def HasSplitCertificate (n : Nat) (p : List Nat) : Prop :=
  ∃ (pref tail : List Nat) (b : Boundary),
    p = pref ++ tail ∧ pref ≠ [] ∧ tail ≠ [] ∧
    Loads b pref [] [] [] ∧ Run tail b.first b.second b.third (target n)

theorem splitCertificate_sorts {n : Nat} {p : List Nat} (h : HasSplitCertificate n p) :
    Sortable n p := by
  obtain ⟨pref, tail, b, rfl, _, _, load, finish⟩ := h
  exact (run_iff_sortsTo _ _).mp (load.continue finish)

/-- Replay instructions 1, 2 and 3 before the cut and compare all three final stacks. -/
def checkLoad (b : Boundary) : List Nat → List Nat → List Nat → List Nat → List Nat → Bool
  | [], [], s, t, u => decide (s = b.first ∧ t = b.second ∧ u = b.third)
  | 1 :: ms, x :: i, s, t, u => checkLoad b ms i (x :: s) t u
  | 2 :: ms, i, x :: s, t, u => checkLoad b ms i s (x :: t) u
  | 3 :: ms, i, s, x :: t, u => checkLoad b ms i s t (x :: u)
  | _, _, _, _, _ => false

theorem checkLoad_sound {b : Boundary} {ms i s t u : List Nat}
    (h : checkLoad b ms i s t u = true) : Loads b i s t u := by
  fun_induction checkLoad <;> simp_all
  all_goals first | exact .done | apply Loads.input <;> assumption
                  | apply Loads.first <;> assumption | apply Loads.second <;> assumption

/-- Check a pair of concrete transfer words independently on the two sides of the cut. -/
theorem splitCertificate_of_words {n : Nat} {pref tail before after : List Nat} {b : Boundary}
    (hp : pref ≠ []) (ht : tail ≠ []) (load : checkLoad b before pref [] [] [] = true)
    (finish : checkRun after tail b.first b.second b.third (target n) = true) :
    HasSplitCertificate n (pref ++ tail) :=
  ⟨pref, tail, b, rfl, hp, ht, checkLoad_sound load, checkRun_sound finish⟩

end ThreeStacks
