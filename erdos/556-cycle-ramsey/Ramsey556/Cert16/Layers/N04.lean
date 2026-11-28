import Ramsey556.Cert16.Layers.N04S0

namespace Ramsey556.Cert16

theorem rows4 : ∀ i, i < (table 4).size → RowGood 4 ((table 4).get i) (table 5) :=
  fun i hi => (show GoodRange 4 0 4 from range4_0) i (Nat.zero_le i) hi

end Ramsey556.Cert16
