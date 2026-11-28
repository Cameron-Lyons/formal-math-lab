import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N01

-- Generated from N02.bin, SHA-256 2216de34f7ea37bb1eb38422dc5cd1334635443688ac6eb46970a644fd18497e.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def row2_0 : List Row := cert16Rows% "../Data/N02.bin" 0 1
private theorem check2_0 : checkChunk 2 (table 2) (table 3) 0 row2_0 = true := by decide +kernel
private theorem good2_0 : GoodRange 2 0 1 :=
  chunk_sound 2 _ _ 0 row2_0 check2_0

theorem range2_0 : GoodRange 2 0 1 :=
  good2_0

end Ramsey556.Cert16
