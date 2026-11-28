import Simple.FiniteTactic
import Simple.Finite05

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace E1486.Simple.Finite.K07

private theorem case1 (g t : G) : (check 7 1 g t && ordered 7 1 g) = false := by check_graph
private theorem case3 (g t : G) : (check 7 3 g t && ordered 7 3 g) = false := by check_graph
private theorem case5 (g t : G) : (check 7 5 g t && ordered 7 5 g) = false := by check_graph
private theorem case7 (g t : G) : (check 7 7 g t && ordered 7 7 g) = false := by check_graph

theorem refute (j : Nat) (hj : j ≤ 7) (hp : (7 - j) % 2 = 0) (g t : G) :
    (check 7 j g t && ordered 7 j g) = false := by
  have h : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact case1 g t
  · exact case3 g t
  · exact case5 g t
  · exact case7 g t

end E1486.Simple.Finite.K07
