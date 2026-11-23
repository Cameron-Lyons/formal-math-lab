import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N02

-- Generated from N03.bin, SHA-256 b9615a951f7b17be2af24bc5e3ee04d16e3ee7a82f12a859b7287019d1b8e88c.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def row3_0 : List Row := cert16Rows% "../Data/N03.bin" 0 2
private theorem check3_0 : checkChunk 3 (table 3) (table 4) 0 row3_0 = true := by decide +kernel
private theorem good3_0 : GoodRange 3 0 2 :=
  chunk_sound 3 _ _ 0 row3_0 check3_0

theorem range3_0 : GoodRange 3 0 2 :=
  good3_0

end Ramsey556.Cert16
