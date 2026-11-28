import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N04

-- Generated from N05.bin, SHA-256 48219918022d2a33da706d4294d1a942fabd170f7dbe7d41e85566e1b276d333.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def row5_0 : List Row := cert16Rows% "../Data/N05.bin" 0 14
private theorem check5_0 : checkChunk 5 (table 5) (table 6) 0 row5_0 = true := by decide +kernel
private theorem good5_0 : GoodRange 5 0 14 :=
  chunk_sound 5 _ _ 0 row5_0 check5_0

theorem range5_0 : GoodRange 5 0 14 :=
  good5_0

end Ramsey556.Cert16
