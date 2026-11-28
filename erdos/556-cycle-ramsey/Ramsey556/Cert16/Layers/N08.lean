import Ramsey556.Cert16.Layers.N08S0
import Ramsey556.Cert16.Layers.N08S1
import Ramsey556.Cert16.Layers.N08S2
import Ramsey556.Cert16.Layers.N08S3

namespace Ramsey556.Cert16

theorem rows8 : ∀ i, i < (table 8).size → RowGood 8 ((table 8).get i) (table 9) :=
  fun i hi => (show GoodRange 8 0 3793 from (joinRanges (joinRanges range8_0 range8_1) (joinRanges range8_2 range8_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
