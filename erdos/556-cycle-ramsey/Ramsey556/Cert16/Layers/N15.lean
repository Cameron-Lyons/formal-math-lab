import Ramsey556.Cert16.Layers.N15S0
import Ramsey556.Cert16.Layers.N15S1
import Ramsey556.Cert16.Layers.N15S2
import Ramsey556.Cert16.Layers.N15S3

namespace Ramsey556.Cert16

theorem rows15 : ∀ i, i < (table 15).size → RowGood 15 ((table 15).get i) (table 16) :=
  fun i hi => (show GoodRange 15 0 48 from (joinRanges (joinRanges range15_0 range15_1) (joinRanges range15_2 range15_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
