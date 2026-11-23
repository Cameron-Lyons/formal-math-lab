import Simple.FiniteTactic
import Simple.Finite09

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace E1486.Simple.Finite.K11

private theorem case1 (g t : G) : (check 11 1 g t && ordered 11 1 g) = false := by check_graph
private theorem case3 (g t : G) : (check 11 3 g t && ordered 11 3 g) = false := by check_graph
private theorem case5 (g t : G) : (check 11 5 g t && ordered 11 5 g) = false := by check_graph
private theorem case7 (g t : G) : (check 11 7 g t && ordered 11 7 g) = false := by check_graph
private theorem case9 (g t : G) : (check 11 9 g t && ordered 11 9 g) = false := by check_graph_unordered
private theorem case11 (g t : G) : (check 11 11 g t && ordered 11 11 g) = false := by check_graph_unordered

theorem refute (j : Nat) (hj : j ≤ 11) (hp : (11 - j) % 2 = 0) (g t : G) :
    (check 11 j g t && ordered 11 j g) = false := by
  have h : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 9 ∨ j = 11 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact case1 g t
  · exact case3 g t
  · exact case5 g t
  · exact case7 g t
  · exact case9 g t
  · exact case11 g t

end E1486.Simple.Finite.K11
