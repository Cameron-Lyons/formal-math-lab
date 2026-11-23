import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N12

-- Generated from N13.bin, SHA-256 d0c43f7abec8c7042ff6029a167dd3a29f53283e2d52fec365908489f885d509.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row13_47 : List Row := cert16Rows% "../Data/N13.bin" 24310 1
private theorem check13_47 : checkChunk 13 (table 13) (table 14) 47 row13_47 = true := by decide +kernel
private theorem good13_47 : GoodRange 13 47 48 :=
  chunk_sound 13 _ _ 47 row13_47 check13_47

private noncomputable def row13_48 : List Row := cert16Rows% "../Data/N13.bin" 26100 3
private theorem check13_48 : checkChunk 13 (table 13) (table 14) 48 row13_48 = true := by decide +kernel
private theorem good13_48 : GoodRange 13 48 51 :=
  chunk_sound 13 _ _ 48 row13_48 check13_48

private noncomputable def row13_51 : List Row := cert16Rows% "../Data/N13.bin" 27654 4
private theorem check13_51 : checkChunk 13 (table 13) (table 14) 51 row13_51 = true := by decide +kernel
private theorem good13_51 : GoodRange 13 51 55 :=
  chunk_sound 13 _ _ 51 row13_51 check13_51

private noncomputable def row13_55 : List Row := cert16Rows% "../Data/N13.bin" 29486 3
private theorem check13_55 : checkChunk 13 (table 13) (table 14) 55 row13_55 = true := by decide +kernel
private theorem good13_55 : GoodRange 13 55 58 :=
  chunk_sound 13 _ _ 55 row13_55 check13_55

private noncomputable def row13_58 : List Row := cert16Rows% "../Data/N13.bin" 31184 6
private theorem check13_58 : checkChunk 13 (table 13) (table 14) 58 row13_58 = true := by decide +kernel
private theorem good13_58 : GoodRange 13 58 64 :=
  chunk_sound 13 _ _ 58 row13_58 check13_58

private noncomputable def row13_64 : List Row := cert16Rows% "../Data/N13.bin" 33164 3
private theorem check13_64 : checkChunk 13 (table 13) (table 14) 64 row13_64 = true := by decide +kernel
private theorem good13_64 : GoodRange 13 64 67 :=
  chunk_sound 13 _ _ 64 row13_64 check13_64

theorem range13_2 : GoodRange 13 47 67 :=
  (joinRanges (joinRanges good13_47 (joinRanges good13_48 good13_51)) (joinRanges good13_55 (joinRanges good13_58 good13_64)))

end Ramsey556.Cert16
