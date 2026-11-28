import Simple.FiniteTactic
import Simple.Finite04

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace E1486.Simple.Finite.K06

private theorem case0 (g t : G) : (check 6 0 g t && ordered 6 0 g) = false := by check_graph
private theorem case2 (g t : G) : (check 6 2 g t && ordered 6 2 g) = false := by check_graph
private theorem case4 (g t : G) : (check 6 4 g t && ordered 6 4 g) = false := by check_graph
private theorem case6 (g t : G) : (check 6 6 g t && ordered 6 6 g) = false := by check_graph

theorem refute (j : Nat) (hj : j ≤ 6) (hp : (6 - j) % 2 = 0) (g t : G) :
    (check 6 j g t && ordered 6 j g) = false := by
  have h : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact case0 g t
  · exact case2 g t
  · exact case4 g t
  · exact case6 g t

end E1486.Simple.Finite.K06
