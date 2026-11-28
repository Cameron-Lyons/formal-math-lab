import Simple.FiniteTactic
import Simple.Finite06

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace E1486.Simple.Finite.K08

private theorem case0 (g t : G) : (check 8 0 g t && ordered 8 0 g) = false := by check_graph
private theorem case2 (g t : G) : (check 8 2 g t && ordered 8 2 g) = false := by check_graph
private theorem case4 (g t : G) : (check 8 4 g t && ordered 8 4 g) = false := by check_graph
private theorem case6 (g t : G) : (check 8 6 g t && ordered 8 6 g) = false := by check_graph
private theorem case8 (g t : G) : (check 8 8 g t && ordered 8 8 g) = false := by check_graph_unordered

theorem refute (j : Nat) (hj : j ≤ 8) (hp : (8 - j) % 2 = 0) (g t : G) :
    (check 8 j g t && ordered 8 j g) = false := by
  have h : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact case0 g t
  · exact case2 g t
  · exact case4 g t
  · exact case6 g t
  · exact case8 g t

end E1486.Simple.Finite.K08
