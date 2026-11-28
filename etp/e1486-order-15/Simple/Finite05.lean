import Simple.FiniteTactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace E1486.Simple.Finite.K05

private theorem case1 (g t : G) : (check 5 1 g t && ordered 5 1 g) = false := by check_graph
private theorem case3 (g t : G) : (check 5 3 g t && ordered 5 3 g) = false := by check_graph
private theorem case5 (g t : G) : (check 5 5 g t && ordered 5 5 g) = false := by check_graph

theorem refute (j : Nat) (hj : j ≤ 5) (hp : (5 - j) % 2 = 0) (g t : G) :
    (check 5 j g t && ordered 5 j g) = false := by
  have h : j = 1 ∨ j = 3 ∨ j = 5 := by omega
  rcases h with rfl | rfl | rfl
  · exact case1 g t
  · exact case3 g t
  · exact case5 g t

end E1486.Simple.Finite.K05
