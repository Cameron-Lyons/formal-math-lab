import Ramsey556.Cert16.Layers.N09S0
import Ramsey556.Cert16.Layers.N09S1
import Ramsey556.Cert16.Layers.N09S2
import Ramsey556.Cert16.Layers.N09S3

namespace Ramsey556.Cert16

theorem rows9 : ∀ i, i < (table 9).size → RowGood 9 ((table 9).get i) (table 10) :=
  fun i hi => (show GoodRange 9 0 6068 from (joinRanges (joinRanges range9_0 range9_1) (joinRanges range9_2 range9_3))) i (Nat.zero_le i) hi

end Ramsey556.Cert16
