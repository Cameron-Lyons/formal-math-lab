import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N14

-- Generated from N15.bin, SHA-256 2e5ff0812ab889916b3098a6c163283f150af6b85ac09e5ef0334da92b98e441.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row15_0 : List Row := cert16Rows% "../Data/N15.bin" 0 5
private theorem check15_0 : checkChunk 15 (table 15) (table 16) 0 row15_0 = true := by decide +kernel
private theorem good15_0 : GoodRange 15 0 5 :=
  chunk_sound 15 _ _ 0 row15_0 check15_0

private noncomputable def row15_5 : List Row := cert16Rows% "../Data/N15.bin" 2210 5
private theorem check15_5 : checkChunk 15 (table 15) (table 16) 5 row15_5 = true := by decide +kernel
private theorem good15_5 : GoodRange 15 5 10 :=
  chunk_sound 15 _ _ 5 row15_5 check15_5

private noncomputable def row15_10 : List Row := cert16Rows% "../Data/N15.bin" 4420 5
private theorem check15_10 : checkChunk 15 (table 15) (table 16) 10 row15_10 = true := by decide +kernel
private theorem good15_10 : GoodRange 15 10 15 :=
  chunk_sound 15 _ _ 10 row15_10 check15_10

theorem range15_0 : GoodRange 15 0 15 :=
  (joinRanges good15_0 (joinRanges good15_5 good15_10))

end Ramsey556.Cert16
