import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N12

-- Generated from N13.bin, SHA-256 d0c43f7abec8c7042ff6029a167dd3a29f53283e2d52fec365908489f885d509.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row13_67 : List Row := cert16Rows% "../Data/N13.bin" 34694 5
private theorem check13_67 : checkChunk 13 (table 13) (table 14) 67 row13_67 = true := by decide +kernel
private theorem good13_67 : GoodRange 13 67 72 :=
  chunk_sound 13 _ _ 67 row13_67 check13_67

private noncomputable def row13_72 : List Row := cert16Rows% "../Data/N13.bin" 36516 7
private theorem check13_72 : checkChunk 13 (table 13) (table 14) 72 row13_72 = true := by decide +kernel
private theorem good13_72 : GoodRange 13 72 79 :=
  chunk_sound 13 _ _ 72 row13_72 check13_72

private noncomputable def row13_79 : List Row := cert16Rows% "../Data/N13.bin" 38674 7
private theorem check13_79 : checkChunk 13 (table 13) (table 14) 79 row13_79 = true := by decide +kernel
private theorem good13_79 : GoodRange 13 79 86 :=
  chunk_sound 13 _ _ 79 row13_79 check13_79

private noncomputable def row13_86 : List Row := cert16Rows% "../Data/N13.bin" 40844 2
private theorem check13_86 : checkChunk 13 (table 13) (table 14) 86 row13_86 = true := by decide +kernel
private theorem good13_86 : GoodRange 13 86 88 :=
  chunk_sound 13 _ _ 86 row13_86 check13_86

private noncomputable def row13_88 : List Row := cert16Rows% "../Data/N13.bin" 43752 2
private theorem check13_88 : checkChunk 13 (table 13) (table 14) 88 row13_88 = true := by decide +kernel
private theorem good13_88 : GoodRange 13 88 90 :=
  chunk_sound 13 _ _ 88 row13_88 check13_88

private noncomputable def row13_90 : List Row := cert16Rows% "../Data/N13.bin" 45392 3
private theorem check13_90 : checkChunk 13 (table 13) (table 14) 90 row13_90 = true := by decide +kernel
private theorem good13_90 : GoodRange 13 90 93 :=
  chunk_sound 13 _ _ 90 row13_90 check13_90

theorem range13_3 : GoodRange 13 67 93 :=
  (joinRanges (joinRanges good13_67 (joinRanges good13_72 good13_79)) (joinRanges good13_86 (joinRanges good13_88 good13_90)))

end Ramsey556.Cert16
