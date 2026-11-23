import Ramsey556.Cert16.Layers.N02S0

namespace Ramsey556.Cert16

theorem rows2 : ∀ i, i < (table 2).size → RowGood 2 ((table 2).get i) (table 3) :=
  fun i hi => (show GoodRange 2 0 1 from range2_0) i (Nat.zero_le i) hi

end Ramsey556.Cert16
