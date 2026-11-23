import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N13

-- Generated from N14.bin, SHA-256 e4792f3081d105374ca7421341455b958d411290184451b835611912c003c81a.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row14_43 : List Row := cert16Rows% "../Data/N14.bin" 20070 2
private theorem check14_43 : checkChunk 14 (table 14) (table 15) 43 row14_43 = true := by decide +kernel
private theorem good14_43 : GoodRange 14 43 45 :=
  chunk_sound 14 _ _ 43 row14_43 check14_43

private noncomputable def row14_45 : List Row := cert16Rows% "../Data/N14.bin" 21710 4
private theorem check14_45 : checkChunk 14 (table 14) (table 15) 45 row14_45 = true := by decide +kernel
private theorem good14_45 : GoodRange 14 45 49 :=
  chunk_sound 14 _ _ 45 row14_45 check14_45

private noncomputable def row14_49 : List Row := cert16Rows% "../Data/N14.bin" 23422 5
private theorem check14_49 : checkChunk 14 (table 14) (table 15) 49 row14_49 = true := by decide +kernel
private theorem good14_49 : GoodRange 14 49 54 :=
  chunk_sound 14 _ _ 49 row14_49 check14_49

private noncomputable def row14_54 : List Row := cert16Rows% "../Data/N14.bin" 25268 5
private theorem check14_54 : checkChunk 14 (table 14) (table 15) 54 row14_54 = true := by decide +kernel
private theorem good14_54 : GoodRange 14 54 59 :=
  chunk_sound 14 _ _ 54 row14_54 check14_54

private noncomputable def row14_59 : List Row := cert16Rows% "../Data/N14.bin" 27114 6
private theorem check14_59 : checkChunk 14 (table 14) (table 15) 59 row14_59 = true := by decide +kernel
private theorem good14_59 : GoodRange 14 59 65 :=
  chunk_sound 14 _ _ 59 row14_59 check14_59

theorem range14_2 : GoodRange 14 43 65 :=
  (joinRanges (joinRanges good14_43 good14_45) (joinRanges good14_49 (joinRanges good14_54 good14_59)))

end Ramsey556.Cert16
