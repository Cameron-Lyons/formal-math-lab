import Height14.Grid
import Height14.Witness
import Height14.ScanBound
import Height14.RefinementCert

namespace Height14

/-- For every positive width the formula is attained by an induced grid path,
    and every induced grid path has at most that many squares. -/
theorem longest_snake (n : Nat) (hn : 0 < n) :
    (∃ cells, Snake n cells ∧ cells.length = formula n) ∧
    (∀ cells, Snake n cells → cells.length ≤ formula n) := by
  refine ⟨lower n hn, ?_⟩
  intro cells snake
  let p := snake.ranked
  have bound := Cert.scanBound Cert.graph Cert.goodRows Cert.goodEnds n
    p.profile p.fills p.initial p.final_accept p.step
  rw [p.count_fills] at bound
  exact Nat.le_of_succ_le_succ (Nat.le_trans bound (Cert.upperStart n))

end Height14
