import Simple.FiniteTactic
import Simple.Finite07

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace E1486.Simple.Finite.K09

private theorem case1 (g t : G) : (check 9 1 g t && ordered 9 1 g) = false := by check_graph
private theorem case3 (g t : G) : (check 9 3 g t && ordered 9 3 g) = false := by check_graph
private theorem case5 (g t : G) : (check 9 5 g t && ordered 9 5 g) = false := by check_graph
private theorem case7 (g t : G) : (check 9 7 g t && ordered 9 7 g) = false := by check_graph
private theorem case9 (g t : G) : (check 9 9 g t && ordered 9 9 g) = false := by check_graph_unordered

theorem refute (j : Nat) (hj : j ≤ 9) (hp : (9 - j) % 2 = 0) (g t : G) :
    (check 9 j g t && ordered 9 j g) = false := by
  have h : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 9 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact case1 g t
  · exact case3 g t
  · exact case5 g t
  · exact case7 g t
  · exact case9 g t

end E1486.Simple.Finite.K09
