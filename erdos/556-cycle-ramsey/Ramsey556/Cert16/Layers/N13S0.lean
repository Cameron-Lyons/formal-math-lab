import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N12

-- Generated from N13.bin, SHA-256 d0c43f7abec8c7042ff6029a167dd3a29f53283e2d52fec365908489f885d509.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row13_0 : List Row := cert16Rows% "../Data/N13.bin" 0 1
private theorem check13_0 : checkChunk 13 (table 13) (table 14) 0 row13_0 = true := by decide +kernel
private theorem good13_0 : GoodRange 13 0 1 :=
  chunk_sound 13 _ _ 0 row13_0 check13_0

private noncomputable def row13_1 : List Row := cert16Rows% "../Data/N13.bin" 1450 2
private theorem check13_1 : checkChunk 13 (table 13) (table 14) 1 row13_1 = true := by decide +kernel
private theorem good13_1 : GoodRange 13 1 3 :=
  chunk_sound 13 _ _ 1 row13_1 check13_1

private noncomputable def row13_3 : List Row := cert16Rows% "../Data/N13.bin" 3230 5
private theorem check13_3 : checkChunk 13 (table 13) (table 14) 3 row13_3 = true := by decide +kernel
private theorem good13_3 : GoodRange 13 3 8 :=
  chunk_sound 13 _ _ 3 row13_3 check13_3

private noncomputable def row13_8 : List Row := cert16Rows% "../Data/N13.bin" 5244 6
private theorem check13_8 : checkChunk 13 (table 13) (table 14) 8 row13_8 = true := by decide +kernel
private theorem good13_8 : GoodRange 13 8 14 :=
  chunk_sound 13 _ _ 8 row13_8 check13_8

private noncomputable def row13_14 : List Row := cert16Rows% "../Data/N13.bin" 7392 7
private theorem check13_14 : checkChunk 13 (table 13) (table 14) 14 row13_14 = true := by decide +kernel
private theorem good13_14 : GoodRange 13 14 21 :=
  chunk_sound 13 _ _ 14 row13_14 check13_14

theorem range13_0 : GoodRange 13 0 21 :=
  (joinRanges (joinRanges good13_0 good13_1) (joinRanges good13_3 (joinRanges good13_8 good13_14)))

end Ramsey556.Cert16
