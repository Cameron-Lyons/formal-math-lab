import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N13

-- Generated from N14.bin, SHA-256 e4792f3081d105374ca7421341455b958d411290184451b835611912c003c81a.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row14_65 : List Row := cert16Rows% "../Data/N14.bin" 29094 4
private theorem check14_65 : checkChunk 14 (table 14) (table 15) 65 row14_65 = true := by decide +kernel
private theorem good14_65 : GoodRange 14 65 69 :=
  chunk_sound 14 _ _ 65 row14_65 check14_65

private noncomputable def row14_69 : List Row := cert16Rows% "../Data/N14.bin" 33918 1
private theorem check14_69 : checkChunk 14 (table 14) (table 15) 69 row14_69 = true := by decide +kernel
private theorem good14_69 : GoodRange 14 69 70 :=
  chunk_sound 14 _ _ 69 row14_69 check14_69

private noncomputable def row14_70 : List Row := cert16Rows% "../Data/N14.bin" 35760 1
private theorem check14_70 : checkChunk 14 (table 14) (table 15) 70 row14_70 = true := by decide +kernel
private theorem good14_70 : GoodRange 14 70 71 :=
  chunk_sound 14 _ _ 70 row14_70 check14_70

private noncomputable def row14_71 : List Row := cert16Rows% "../Data/N14.bin" 38774 2
private theorem check14_71 : checkChunk 14 (table 14) (table 15) 71 row14_71 = true := by decide +kernel
private theorem good14_71 : GoodRange 14 71 73 :=
  chunk_sound 14 _ _ 71 row14_71 check14_71

private noncomputable def row14_73 : List Row := cert16Rows% "../Data/N14.bin" 40718 3
private theorem check14_73 : checkChunk 14 (table 14) (table 15) 73 row14_73 = true := by decide +kernel
private theorem good14_73 : GoodRange 14 73 76 :=
  chunk_sound 14 _ _ 73 row14_73 check14_73

private noncomputable def row14_76 : List Row := cert16Rows% "../Data/N14.bin" 42124 5
private theorem check14_76 : checkChunk 14 (table 14) (table 15) 76 row14_76 = true := by decide +kernel
private theorem good14_76 : GoodRange 14 76 81 :=
  chunk_sound 14 _ _ 76 row14_76 check14_76

theorem range14_3 : GoodRange 14 65 81 :=
  (joinRanges (joinRanges good14_65 (joinRanges good14_69 good14_70)) (joinRanges good14_71 (joinRanges good14_73 good14_76)))

end Ramsey556.Cert16
