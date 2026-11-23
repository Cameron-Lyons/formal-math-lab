import BlockLCM
import Bounded
import Displacement
import Gap
import Height
import Initial
import Period
import Shift
import SixCubics
import SixElliptic

namespace Erdos677
open Finset

/-- A kernel-checked exclusion with no endpoint bound: every disjoint
equal-length pair of blocks whose starts differ by at most 52. -/
theorem no_collision_shift_le_52 {n m k : ℕ} (hk : 0 < k) (hd : n+k ≤ m)
    (hD : m ≤ n+52) : lcmInterval m k ≠ lcmInterval n k := by
  intro heq
  apply no_collision_through_1000 hk hd _ heq
  apply endpoint_le_of_bounds_check hk hd hD heq
  decide +kernel

end Erdos677
