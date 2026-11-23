import Ramsey556.Cert16.Layers.N01S0

namespace Ramsey556.Cert16

theorem rows1 : ∀ i, i < (table 1).size → RowGood 1 ((table 1).get i) (table 2) :=
  fun i hi => (show GoodRange 1 0 1 from range1_0) i (Nat.zero_le i) hi

end Ramsey556.Cert16
