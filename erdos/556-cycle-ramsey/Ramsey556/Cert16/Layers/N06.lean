import Ramsey556.Cert16.Layers.N06S0
import Ramsey556.Cert16.Layers.N06S1
import Ramsey556.Cert16.Layers.N06S2
import Ramsey556.Cert16.Layers.N06S3

namespace Ramsey556.Cert16

theorem rows6 : ∀ i, i < (table 6).size → RowGood 6 ((table 6).get i) (table 7) :=
  fun i hi => (show GoodRange 6 0 54 from (joinRanges (joinRanges range6_0 range6_1) (joinRanges range6_2 range6_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
