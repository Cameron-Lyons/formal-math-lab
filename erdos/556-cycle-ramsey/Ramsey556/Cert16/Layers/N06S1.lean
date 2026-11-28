import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N05

-- Generated from N06.bin, SHA-256 0fc4e085c7baa6508f4dbb22626667a0fe61baed2c80ae17aee2427cfdc61282.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def row6_14 : List Row := cert16Rows% "../Data/N06.bin" 24892 16
private theorem check6_14 : checkChunk 6 (table 6) (table 7) 14 row6_14 = true := by decide +kernel
private theorem good6_14 : GoodRange 6 14 30 :=
  chunk_sound 6 _ _ 14 row6_14 check6_14

theorem range6_1 : GoodRange 6 14 30 :=
  good6_14

end Ramsey556.Cert16
