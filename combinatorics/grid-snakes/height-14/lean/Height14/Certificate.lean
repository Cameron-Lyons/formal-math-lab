import Height14.Graph
import Height14.ScoreCheck

namespace Height14.Cert

/-- Lean's native evaluator checks 644 backwards steps and every coordinate
of the six-column upper inequality. -/
theorem scores_checked : checkScores graph = true := by native_decide

theorem base {n : Nat} (hn : n ≤ 46) :
    (vals graph (14*n)).getD 0 0 ≤ formula n + 1 :=
  check_base scores_checked hn

theorem period (i : Nat) :
    (vals graph (14*46)).getD i 0 ≤ shift 52 ((vals graph (14*40)).getD i 0) :=
  check_period scores_checked i

end Height14.Cert
