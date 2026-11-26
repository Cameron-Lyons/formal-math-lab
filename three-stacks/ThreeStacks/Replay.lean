import ThreeStacks.Machine

namespace ThreeStacks

/-- Instructions 1 through 4 each move one card one place to the right. -/
def checkRun : List Nat → List Nat → List Nat → List Nat → List Nat → List Nat → Bool
  | [], [], [], [], [], [] => true
  | 1 :: ms, x :: i, s, t, u, o => checkRun ms i (x :: s) t u o
  | 2 :: ms, i, x :: s, t, u, o => checkRun ms i s (x :: t) u o
  | 3 :: ms, i, s, x :: t, u, o => checkRun ms i s t (x :: u) o
  | 4 :: ms, i, s, t, x :: u, y :: o => x == y && checkRun ms i s t u o
  | _, _, _, _, _, _ => false

theorem checkRun_sound {ms i s t u o} (h : checkRun ms i s t u o = true) :
    Run i s t u o := by
  fun_induction checkRun <;> simp_all
  all_goals first | exact .done | apply Run.input <;> assumption
                  | apply Run.first <;> assumption | apply Run.second <;> assumption
                  | apply Run.output <;> assumption

end ThreeStacks
