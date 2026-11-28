import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N14

-- Generated from N15.bin, SHA-256 2e5ff0812ab889916b3098a6c163283f150af6b85ac09e5ef0334da92b98e441.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row15_40 : List Row := cert16Rows% "../Data/N15.bin" 29272 1
private theorem check15_40 : checkChunk 15 (table 15) (table 16) 40 row15_40 = true := by decide +kernel
private theorem good15_40 : GoodRange 15 40 41 :=
  chunk_sound 15 _ _ 40 row15_40 check15_40

private noncomputable def row15_41 : List Row := cert16Rows% "../Data/N15.bin" 30778 3
private theorem check15_41 : checkChunk 15 (table 15) (table 16) 41 row15_41 = true := by decide +kernel
private theorem good15_41 : GoodRange 15 41 44 :=
  chunk_sound 15 _ _ 41 row15_41 check15_41

private noncomputable def row15_44 : List Row := cert16Rows% "../Data/N15.bin" 35736 2
private theorem check15_44 : checkChunk 15 (table 15) (table 16) 44 row15_44 = true := by decide +kernel
private theorem good15_44 : GoodRange 15 44 46 :=
  chunk_sound 15 _ _ 44 row15_44 check15_44

private noncomputable def row15_46 : List Row := cert16Rows% "../Data/N15.bin" 37788 2
private theorem check15_46 : checkChunk 15 (table 15) (table 16) 46 row15_46 = true := by decide +kernel
private theorem good15_46 : GoodRange 15 46 48 :=
  chunk_sound 15 _ _ 46 row15_46 check15_46

theorem range15_3 : GoodRange 15 40 48 :=
  (joinRanges (joinRanges good15_40 good15_41) (joinRanges good15_44 good15_46))

end Ramsey556.Cert16
