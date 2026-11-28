import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N05

-- Generated from N06.bin, SHA-256 0fc4e085c7baa6508f4dbb22626667a0fe61baed2c80ae17aee2427cfdc61282.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def row6_30 : List Row := cert16Rows% "../Data/N06.bin" 48960 17
private theorem check6_30 : checkChunk 6 (table 6) (table 7) 30 row6_30 = true := by decide +kernel
private theorem good6_30 : GoodRange 6 30 47 :=
  chunk_sound 6 _ _ 30 row6_30 check6_30

theorem range6_2 : GoodRange 6 30 47 :=
  good6_30

end Ramsey556.Cert16
