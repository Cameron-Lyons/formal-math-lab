import ThreeStacks.Model

namespace ThreeStacks

/-- The four permitted physical moves. All three stacks start and finish empty
    in a sorting run. The output list is in chronological order. -/
inductive Run : List Nat → List Nat → List Nat → List Nat → List Nat → Prop where
  | done : Run [] [] [] [] []
  | input : Run i (x :: s) t u o → Run (x :: i) s t u o
  | first : Run i s (x :: t) u o → Run i (x :: s) t u o
  | second : Run i s t (x :: u) o → Run i s (x :: t) u o
  | output : Run i s t u o → Run i s t (x :: u) (x :: o)

private theorem project (h : Run i s t u o) :
    ∃ A B, Pass i s A ∧ Pass A t B ∧ Pass B u o := by
  induction h with
  | done => exact ⟨[], [], .done, .done, .done⟩
  | input _ ih =>
    obtain ⟨A, B, a, b, c⟩ := ih
    exact ⟨A, B, .push a, b, c⟩
  | first _ ih =>
    obtain ⟨A, B, a, b, c⟩ := ih
    exact ⟨_, B, .pop a, .push b, c⟩
  | second _ ih =>
    obtain ⟨A, B, a, b, c⟩ := ih
    exact ⟨A, _, a, .pop b, .push c⟩
  | output _ ih =>
    obtain ⟨A, B, a, b, c⟩ := ih
    exact ⟨A, B, a, b, .pop c⟩

private theorem pass_length (h : Pass i s o) : i.length + s.length = o.length := by
  induction h <;> simp_all <;> omega

/-- Schedule the next move by servicing the most downstream stack first. -/
private theorem interleave {i s t u o A B : List Nat}
    (a : Pass i s A) (b : Pass A t B) (c : Pass B u o) : Run i s t u o := by
  cases c with
  | done =>
    have hb := pass_length b
    simp only [List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have ha := pass_length a
    simp only [List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact .done
  | pop c' => exact .output (interleave a b c')
  | push c' =>
    cases b with
    | pop b' => exact .second (interleave a b' c')
    | push b' =>
      cases a with
      | pop a' => exact .first (interleave a' b' (.push c'))
      | push a' => exact .input (interleave a' (.push b') (.push c'))
termination_by 4 * i.length + 3 * s.length + 2 * t.length + u.length
decreasing_by all_goals subst_vars <;> simp_all <;> omega

theorem run_iff_sortsTo (p q : List Nat) : Run p [] [] [] q ↔ SortsTo p q := by
  constructor
  · exact project
  · rintro ⟨_, _, a, b, c⟩
    exact interleave a b c

end ThreeStacks
