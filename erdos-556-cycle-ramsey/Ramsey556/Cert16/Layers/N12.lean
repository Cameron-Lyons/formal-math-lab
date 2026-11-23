import Ramsey556.Cert16.Layers.N12S0
import Ramsey556.Cert16.Layers.N12S1
import Ramsey556.Cert16.Layers.N12S2
import Ramsey556.Cert16.Layers.N12S3

namespace Ramsey556.Cert16

theorem rows12 : ∀ i, i < (table 12).size → RowGood 12 ((table 12).get i) (table 13) :=
  fun i hi => (show GoodRange 12 0 319 from (joinRanges (joinRanges range12_0 range12_1) (joinRanges range12_2 range12_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
