import Simple.Finite04
import Simple.Finite05
import Simple.Finite06
import Simple.Finite07
import Simple.Finite08
import Simple.Finite09
import Simple.Finite10
import Simple.Finite11

namespace E1486.Simple.Finite

theorem middle_refute (k j : Nat) (hk : 4 ≤ k) (hn : k ≤ 11) (hj : j ≤ k) (hp : (k-j)%2 = 0)
    (g t : G) : (check k j g t && ordered k j g) = false := by
  have h : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact K04.refute j hj hp g t
  · exact K05.refute j hj hp g t
  · exact K06.refute j hj hp g t
  · exact K07.refute j hj hp g t
  · exact K08.refute j hj hp g t
  · exact K09.refute j hj hp g t
  · exact K10.refute j hj hp g t
  · exact K11.refute j hj hp g t

end E1486.Simple.Finite
