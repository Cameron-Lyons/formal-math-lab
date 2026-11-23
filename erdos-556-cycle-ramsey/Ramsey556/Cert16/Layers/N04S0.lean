import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N03

-- Generated from N04.bin, SHA-256 034ca4482c6e8309c6a4e5163130a7d067e4e65a345798fa957df8b4e182b861.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def row4_0 : List Row := cert16Rows% "../Data/N04.bin" 0 4
private theorem check4_0 : checkChunk 4 (table 4) (table 5) 0 row4_0 = true := by decide +kernel
private theorem good4_0 : GoodRange 4 0 4 :=
  chunk_sound 4 _ _ 0 row4_0 check4_0

theorem range4_0 : GoodRange 4 0 4 :=
  good4_0

end Ramsey556.Cert16
