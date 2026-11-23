import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N14

-- Generated from N15.bin, SHA-256 2e5ff0812ab889916b3098a6c163283f150af6b85ac09e5ef0334da92b98e441.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row15_35 : List Row := cert16Rows% "../Data/N15.bin" 15470 1
private theorem check15_35 : checkChunk 15 (table 15) (table 16) 35 row15_35 = true := by decide +kernel
private theorem good15_35 : GoodRange 15 35 36 :=
  chunk_sound 15 _ _ 35 row15_35 check15_35

private noncomputable def row15_36 : List Row := cert16Rows% "../Data/N15.bin" 22072 1
private theorem check15_36 : checkChunk 15 (table 15) (table 16) 36 row15_36 = true := by decide +kernel
private theorem good15_36 : GoodRange 15 36 37 :=
  chunk_sound 15 _ _ 36 row15_36 check15_36

private noncomputable def row15_37 : List Row := cert16Rows% "../Data/N15.bin" 25734 1
private theorem check15_37 : checkChunk 15 (table 15) (table 16) 37 row15_37 = true := by decide +kernel
private theorem good15_37 : GoodRange 15 37 38 :=
  chunk_sound 15 _ _ 37 row15_37 check15_37

private noncomputable def row15_38 : List Row := cert16Rows% "../Data/N15.bin" 27240 2
private theorem check15_38 : checkChunk 15 (table 15) (table 16) 38 row15_38 = true := by decide +kernel
private theorem good15_38 : GoodRange 15 38 40 :=
  chunk_sound 15 _ _ 38 row15_38 check15_38

theorem range15_2 : GoodRange 15 35 40 :=
  (joinRanges (joinRanges good15_35 good15_36) (joinRanges good15_37 good15_38))

end Ramsey556.Cert16
