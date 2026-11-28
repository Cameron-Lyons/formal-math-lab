import Ramsey556.Cert16.Layers.N07S0
import Ramsey556.Cert16.Layers.N07S1
import Ramsey556.Cert16.Layers.N07S2
import Ramsey556.Cert16.Layers.N07S3

namespace Ramsey556.Cert16

theorem rows7 : ∀ i, i < (table 7).size → RowGood 7 ((table 7).get i) (table 8) :=
  fun i hi => (show GoodRange 7 0 374 from (joinRanges (joinRanges range7_0 range7_1) (joinRanges range7_2 range7_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
