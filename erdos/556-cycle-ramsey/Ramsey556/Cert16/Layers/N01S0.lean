import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges

-- Generated from N01.bin, SHA-256 bb2a990650309582d9097b3225742079c1d52ae02ead9b4b862e6caa5897bfb8.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def row1_0 : List Row := cert16Rows% "../Data/N01.bin" 0 1
private theorem check1_0 : checkChunk 1 (table 1) (table 2) 0 row1_0 = true := by decide +kernel
private theorem good1_0 : GoodRange 1 0 1 :=
  chunk_sound 1 _ _ 0 row1_0 check1_0

theorem range1_0 : GoodRange 1 0 1 :=
  good1_0

end Ramsey556.Cert16
