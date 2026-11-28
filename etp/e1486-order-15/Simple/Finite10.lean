import Simple.FiniteTactic
import Simple.Finite08

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace E1486.Simple.Finite.K10

private theorem case0 (g t : G) : (check 10 0 g t && ordered 10 0 g) = false := by check_graph
private theorem case2 (g t : G) : (check 10 2 g t && ordered 10 2 g) = false := by check_graph
private theorem case4 (g t : G) : (check 10 4 g t && ordered 10 4 g) = false := by check_graph
private theorem case6 (g t : G) : (check 10 6 g t && ordered 10 6 g) = false := by check_graph
private theorem case8 (g t : G) : (check 10 8 g t && ordered 10 8 g) = false := by check_graph_unordered
private theorem case10 (g t : G) : (check 10 10 g t && ordered 10 10 g) = false := by check_graph_unordered

theorem refute (j : Nat) (hj : j ≤ 10) (hp : (10 - j) % 2 = 0) (g t : G) :
    (check 10 j g t && ordered 10 j g) = false := by
  have h : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact case0 g t
  · exact case2 g t
  · exact case4 g t
  · exact case6 g t
  · exact case8 g t
  · exact case10 g t

end E1486.Simple.Finite.K10
