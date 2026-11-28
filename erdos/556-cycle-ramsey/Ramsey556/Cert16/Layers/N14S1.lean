import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N13

-- Generated from N14.bin, SHA-256 e4792f3081d105374ca7421341455b958d411290184451b835611912c003c81a.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row14_16 : List Row := cert16Rows% "../Data/N14.bin" 9592 6
private theorem check14_16 : checkChunk 14 (table 14) (table 15) 16 row14_16 = true := by decide +kernel
private theorem good14_16 : GoodRange 14 16 22 :=
  chunk_sound 14 _ _ 16 row14_16 check14_16

private noncomputable def row14_22 : List Row := cert16Rows% "../Data/N14.bin" 11572 4
private theorem check14_22 : checkChunk 14 (table 14) (table 15) 22 row14_22 = true := by decide +kernel
private theorem good14_22 : GoodRange 14 22 26 :=
  chunk_sound 14 _ _ 22 row14_22 check14_22

private noncomputable def row14_26 : List Row := cert16Rows% "../Data/N14.bin" 13284 5
private theorem check14_26 : checkChunk 14 (table 14) (table 15) 26 row14_26 = true := by decide +kernel
private theorem good14_26 : GoodRange 14 26 31 :=
  chunk_sound 14 _ _ 26 row14_26 check14_26

private noncomputable def row14_31 : List Row := cert16Rows% "../Data/N14.bin" 15326 6
private theorem check14_31 : checkChunk 14 (table 14) (table 15) 31 row14_31 = true := by decide +kernel
private theorem good14_31 : GoodRange 14 31 37 :=
  chunk_sound 14 _ _ 31 row14_31 check14_31

private noncomputable def row14_37 : List Row := cert16Rows% "../Data/N14.bin" 17306 6
private theorem check14_37 : checkChunk 14 (table 14) (table 15) 37 row14_37 = true := by decide +kernel
private theorem good14_37 : GoodRange 14 37 43 :=
  chunk_sound 14 _ _ 37 row14_37 check14_37

theorem range14_1 : GoodRange 14 16 43 :=
  (joinRanges (joinRanges good14_16 good14_22) (joinRanges good14_26 (joinRanges good14_31 good14_37)))

end Ramsey556.Cert16
