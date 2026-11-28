import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N06

-- Generated from N07.bin, SHA-256 b53b70c2f56a30aa7049c83809718dd1441ae04b2f5bd5669e1a6117dc25cd21.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private def row7_75 : List Row := cert16Rows% "../Data/N07.bin" 254602 6
private theorem check7_75 : checkChunk 7 (table 7) (table 8) 75 row7_75 = true := by decide +kernel
private theorem good7_75 : GoodRange 7 75 81 :=
  chunk_sound 7 _ _ 75 row7_75 check7_75

private def row7_81 : List Row := cert16Rows% "../Data/N07.bin" 275286 6
private theorem check7_81 : checkChunk 7 (table 7) (table 8) 81 row7_81 = true := by decide +kernel
private theorem good7_81 : GoodRange 7 81 87 :=
  chunk_sound 7 _ _ 81 row7_81 check7_81

private def row7_87 : List Row := cert16Rows% "../Data/N07.bin" 293814 6
private theorem check7_87 : checkChunk 7 (table 7) (table 8) 87 row7_87 = true := by decide +kernel
private theorem good7_87 : GoodRange 7 87 93 :=
  chunk_sound 7 _ _ 87 row7_87 check7_87

private def row7_93 : List Row := cert16Rows% "../Data/N07.bin" 313630 6
private theorem check7_93 : checkChunk 7 (table 7) (table 8) 93 row7_93 = true := by decide +kernel
private theorem good7_93 : GoodRange 7 93 99 :=
  chunk_sound 7 _ _ 93 row7_93 check7_93

private def row7_99 : List Row := cert16Rows% "../Data/N07.bin" 335098 6
private theorem check7_99 : checkChunk 7 (table 7) (table 8) 99 row7_99 = true := by decide +kernel
private theorem good7_99 : GoodRange 7 99 105 :=
  chunk_sound 7 _ _ 99 row7_99 check7_99

private def row7_105 : List Row := cert16Rows% "../Data/N07.bin" 355978 6
private theorem check7_105 : checkChunk 7 (table 7) (table 8) 105 row7_105 = true := by decide +kernel
private theorem good7_105 : GoodRange 7 105 111 :=
  chunk_sound 7 _ _ 105 row7_105 check7_105

private def row7_111 : List Row := cert16Rows% "../Data/N07.bin" 375682 7
private theorem check7_111 : checkChunk 7 (table 7) (table 8) 111 row7_111 = true := by decide +kernel
private theorem good7_111 : GoodRange 7 111 118 :=
  chunk_sound 7 _ _ 111 row7_111 check7_111

private def row7_118 : List Row := cert16Rows% "../Data/N07.bin" 396416 7
private theorem check7_118 : checkChunk 7 (table 7) (table 8) 118 row7_118 = true := by decide +kernel
private theorem good7_118 : GoodRange 7 118 125 :=
  chunk_sound 7 _ _ 118 row7_118 check7_118

private def row7_125 : List Row := cert16Rows% "../Data/N07.bin" 417346 7
private theorem check7_125 : checkChunk 7 (table 7) (table 8) 125 row7_125 = true := by decide +kernel
private theorem good7_125 : GoodRange 7 125 132 :=
  chunk_sound 7 _ _ 125 row7_125 check7_125

private def row7_132 : List Row := cert16Rows% "../Data/N07.bin" 436904 9
private theorem check7_132 : checkChunk 7 (table 7) (table 8) 132 row7_132 = true := by decide +kernel
private theorem good7_132 : GoodRange 7 132 141 :=
  chunk_sound 7 _ _ 132 row7_132 check7_132

private def row7_141 : List Row := cert16Rows% "../Data/N07.bin" 457738 7
private theorem check7_141 : checkChunk 7 (table 7) (table 8) 141 row7_141 = true := by decide +kernel
private theorem good7_141 : GoodRange 7 141 148 :=
  chunk_sound 7 _ _ 141 row7_141 check7_141

private def row7_148 : List Row := cert16Rows% "../Data/N07.bin" 478472 8
private theorem check7_148 : checkChunk 7 (table 7) (table 8) 148 row7_148 = true := by decide +kernel
private theorem good7_148 : GoodRange 7 148 156 :=
  chunk_sound 7 _ _ 148 row7_148 check7_148

private def row7_156 : List Row := cert16Rows% "../Data/N07.bin" 497884 10
private theorem check7_156 : checkChunk 7 (table 7) (table 8) 156 row7_156 = true := by decide +kernel
private theorem good7_156 : GoodRange 7 156 166 :=
  chunk_sound 7 _ _ 156 row7_156 check7_156

theorem range7_1 : GoodRange 7 75 166 :=
  (joinRanges (joinRanges (joinRanges good7_75 (joinRanges good7_81 good7_87)) (joinRanges good7_93 (joinRanges good7_99 good7_105))) (joinRanges (joinRanges good7_111 (joinRanges good7_118 good7_125)) (joinRanges (joinRanges good7_132 good7_141) (joinRanges good7_148 good7_156))))

end Ramsey556.Cert16
