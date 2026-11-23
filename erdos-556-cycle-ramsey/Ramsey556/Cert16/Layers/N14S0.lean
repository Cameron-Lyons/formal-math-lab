import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N13

-- Generated from N14.bin, SHA-256 e4792f3081d105374ca7421341455b958d411290184451b835611912c003c81a.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row14_0 : List Row := cert16Rows% "../Data/N14.bin" 0 1
private theorem check14_0 : checkChunk 14 (table 14) (table 15) 0 row14_0 = true := by decide +kernel
private theorem good14_0 : GoodRange 14 0 1 :=
  chunk_sound 14 _ _ 0 row14_0 check14_0

private noncomputable def row14_1 : List Row := cert16Rows% "../Data/N14.bin" 2094 2
private theorem check14_1 : checkChunk 14 (table 14) (table 15) 1 row14_1 = true := by decide +kernel
private theorem good14_1 : GoodRange 14 1 3 :=
  chunk_sound 14 _ _ 1 row14_1 check14_1

private noncomputable def row14_3 : List Row := cert16Rows% "../Data/N14.bin" 4322 4
private theorem check14_3 : checkChunk 14 (table 14) (table 15) 3 row14_3 = true := by decide +kernel
private theorem good14_3 : GoodRange 14 3 7 :=
  chunk_sound 14 _ _ 3 row14_3 check14_3

private noncomputable def row14_7 : List Row := cert16Rows% "../Data/N14.bin" 6034 4
private theorem check14_7 : checkChunk 14 (table 14) (table 15) 7 row14_7 = true := by decide +kernel
private theorem good14_7 : GoodRange 14 7 11 :=
  chunk_sound 14 _ _ 7 row14_7 check14_7

private noncomputable def row14_11 : List Row := cert16Rows% "../Data/N14.bin" 7746 5
private theorem check14_11 : checkChunk 14 (table 14) (table 15) 11 row14_11 = true := by decide +kernel
private theorem good14_11 : GoodRange 14 11 16 :=
  chunk_sound 14 _ _ 11 row14_11 check14_11

theorem range14_0 : GoodRange 14 0 16 :=
  (joinRanges (joinRanges good14_0 good14_1) (joinRanges good14_3 (joinRanges good14_7 good14_11)))

end Ramsey556.Cert16
