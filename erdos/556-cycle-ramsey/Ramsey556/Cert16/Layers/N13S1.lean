import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N12

-- Generated from N13.bin, SHA-256 d0c43f7abec8c7042ff6029a167dd3a29f53283e2d52fec365908489f885d509.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row13_21 : List Row := cert16Rows% "../Data/N13.bin" 9506 3
private theorem check13_21 : checkChunk 13 (table 13) (table 14) 21 row13_21 = true := by decide +kernel
private theorem good13_21 : GoodRange 13 21 24 :=
  chunk_sound 13 _ _ 21 row13_21 check13_21

private noncomputable def row13_24 : List Row := cert16Rows% "../Data/N13.bin" 11336 6
private theorem check13_24 : checkChunk 13 (table 13) (table 14) 24 row13_24 = true := by decide +kernel
private theorem good13_24 : GoodRange 13 24 30 :=
  chunk_sound 13 _ _ 24 row13_24 check13_24

private noncomputable def row13_30 : List Row := cert16Rows% "../Data/N13.bin" 13736 5
private theorem check13_30 : checkChunk 13 (table 13) (table 14) 30 row13_30 = true := by decide +kernel
private theorem good13_30 : GoodRange 13 30 35 :=
  chunk_sound 13 _ _ 30 row13_30 check13_30

private noncomputable def row13_35 : List Row := cert16Rows% "../Data/N13.bin" 15582 6
private theorem check13_35 : checkChunk 13 (table 13) (table 14) 35 row13_35 = true := by decide +kernel
private theorem good13_35 : GoodRange 13 35 41 :=
  chunk_sound 13 _ _ 35 row13_35 check13_35

private noncomputable def row13_41 : List Row := cert16Rows% "../Data/N13.bin" 17562 5
private theorem check13_41 : checkChunk 13 (table 13) (table 14) 41 row13_41 = true := by decide +kernel
private theorem good13_41 : GoodRange 13 41 46 :=
  chunk_sound 13 _ _ 41 row13_41 check13_41

private noncomputable def row13_46 : List Row := cert16Rows% "../Data/N13.bin" 22520 1
private theorem check13_46 : checkChunk 13 (table 13) (table 14) 46 row13_46 = true := by decide +kernel
private theorem good13_46 : GoodRange 13 46 47 :=
  chunk_sound 13 _ _ 46 row13_46 check13_46

theorem range13_1 : GoodRange 13 21 47 :=
  (joinRanges (joinRanges good13_21 (joinRanges good13_24 good13_30)) (joinRanges good13_35 (joinRanges good13_41 good13_46)))

end Ramsey556.Cert16
