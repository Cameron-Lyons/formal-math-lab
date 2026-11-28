import Ramsey556.Cert16.Layers.N13S0
import Ramsey556.Cert16.Layers.N13S1
import Ramsey556.Cert16.Layers.N13S2
import Ramsey556.Cert16.Layers.N13S3

namespace Ramsey556.Cert16

theorem rows13 : ∀ i, i < (table 13).size → RowGood 13 ((table 13).get i) (table 14) :=
  fun i hi => (show GoodRange 13 0 93 from (joinRanges (joinRanges range13_0 range13_1) (joinRanges range13_2 range13_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
