import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N14

-- Generated from N15.bin, SHA-256 2e5ff0812ab889916b3098a6c163283f150af6b85ac09e5ef0334da92b98e441.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row15_15 : List Row := cert16Rows% "../Data/N15.bin" 6630 5
private theorem check15_15 : checkChunk 15 (table 15) (table 16) 15 row15_15 = true := by decide +kernel
private theorem good15_15 : GoodRange 15 15 20 :=
  chunk_sound 15 _ _ 15 row15_15 check15_15

private noncomputable def row15_20 : List Row := cert16Rows% "../Data/N15.bin" 8840 5
private theorem check15_20 : checkChunk 15 (table 15) (table 16) 20 row15_20 = true := by decide +kernel
private theorem good15_20 : GoodRange 15 20 25 :=
  chunk_sound 15 _ _ 20 row15_20 check15_20

private noncomputable def row15_25 : List Row := cert16Rows% "../Data/N15.bin" 11050 5
private theorem check15_25 : checkChunk 15 (table 15) (table 16) 25 row15_25 = true := by decide +kernel
private theorem good15_25 : GoodRange 15 25 30 :=
  chunk_sound 15 _ _ 25 row15_25 check15_25

private noncomputable def row15_30 : List Row := cert16Rows% "../Data/N15.bin" 13260 5
private theorem check15_30 : checkChunk 15 (table 15) (table 16) 30 row15_30 = true := by decide +kernel
private theorem good15_30 : GoodRange 15 30 35 :=
  chunk_sound 15 _ _ 30 row15_30 check15_30

theorem range15_1 : GoodRange 15 15 35 :=
  (joinRanges (joinRanges good15_15 good15_20) (joinRanges good15_25 good15_30))

end Ramsey556.Cert16
