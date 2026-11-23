import Ramsey556.Cert16.Layers.N14S0
import Ramsey556.Cert16.Layers.N14S1
import Ramsey556.Cert16.Layers.N14S2
import Ramsey556.Cert16.Layers.N14S3

namespace Ramsey556.Cert16

theorem rows14 : ∀ i, i < (table 14).size → RowGood 14 ((table 14).get i) (table 15) :=
  fun i hi => (show GoodRange 14 0 81 from (joinRanges (joinRanges range14_0 range14_1) (joinRanges range14_2 range14_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
