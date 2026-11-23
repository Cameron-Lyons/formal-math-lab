import Ramsey556.Cert16.Layers.N10S0
import Ramsey556.Cert16.Layers.N10S1
import Ramsey556.Cert16.Layers.N10S2
import Ramsey556.Cert16.Layers.N10S3

namespace Ramsey556.Cert16

theorem rows10 : ∀ i, i < (table 10).size → RowGood 10 ((table 10).get i) (table 11) :=
  fun i hi => (show GoodRange 10 0 3953 from (joinRanges (joinRanges range10_0 range10_1) (joinRanges range10_2 range10_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
