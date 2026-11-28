import Ramsey556.Cert16.Layers.N03S0

namespace Ramsey556.Cert16

theorem rows3 : ∀ i, i < (table 3).size → RowGood 3 ((table 3).get i) (table 4) :=
  fun i hi => (show GoodRange 3 0 2 from range3_0) i (Nat.zero_le i) hi

end Ramsey556.Cert16
