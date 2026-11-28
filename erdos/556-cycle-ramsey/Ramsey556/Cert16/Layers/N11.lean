import Ramsey556.Cert16.Layers.N11S0
import Ramsey556.Cert16.Layers.N11S1
import Ramsey556.Cert16.Layers.N11S2
import Ramsey556.Cert16.Layers.N11S3

namespace Ramsey556.Cert16

theorem rows11 : ∀ i, i < (table 11).size → RowGood 11 ((table 11).get i) (table 12) :=
  fun i hi => (show GoodRange 11 0 816 from (joinRanges (joinRanges range11_0 range11_1) (joinRanges range11_2 range11_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
