import Ramsey556.Cert16.Layers.N05S0

namespace Ramsey556.Cert16

theorem rows5 : ∀ i, i < (table 5).size → RowGood 5 ((table 5).get i) (table 6) :=
  fun i hi => (show GoodRange 5 0 14 from range5_0) i (Nat.zero_le i) hi

end Ramsey556.Cert16
