import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N06

-- Generated from N07.bin, SHA-256 b53b70c2f56a30aa7049c83809718dd1441ae04b2f5bd5669e1a6117dc25cd21.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private def row7_0 : List Row := cert16Rows% "../Data/N07.bin" 0 5
private theorem check7_0 : checkChunk 7 (table 7) (table 8) 0 row7_0 = true := by decide +kernel
private theorem good7_0 : GoodRange 7 0 5 :=
  chunk_sound 7 _ _ 0 row7_0 check7_0

private def row7_5 : List Row := cert16Rows% "../Data/N07.bin" 18030 5
private theorem check7_5 : checkChunk 7 (table 7) (table 8) 5 row7_5 = true := by decide +kernel
private theorem good7_5 : GoodRange 7 5 10 :=
  chunk_sound 7 _ _ 5 row7_5 check7_5

private def row7_10 : List Row := cert16Rows% "../Data/N07.bin" 36032 5
private theorem check7_10 : checkChunk 7 (table 7) (table 8) 10 row7_10 = true := by decide +kernel
private theorem good7_10 : GoodRange 7 10 15 :=
  chunk_sound 7 _ _ 10 row7_10 check7_10

private def row7_15 : List Row := cert16Rows% "../Data/N07.bin" 54062 6
private theorem check7_15 : checkChunk 7 (table 7) (table 8) 15 row7_15 = true := by decide +kernel
private theorem good7_15 : GoodRange 7 15 21 :=
  chunk_sound 7 _ _ 15 row7_15 check7_15

private def row7_21 : List Row := cert16Rows% "../Data/N07.bin" 75418 5
private theorem check7_21 : checkChunk 7 (table 7) (table 8) 21 row7_21 = true := by decide +kernel
private theorem good7_21 : GoodRange 7 21 26 :=
  chunk_sound 7 _ _ 21 row7_21 check7_21

private def row7_26 : List Row := cert16Rows% "../Data/N07.bin" 93448 6
private theorem check7_26 : checkChunk 7 (table 7) (table 8) 26 row7_26 = true := by decide +kernel
private theorem good7_26 : GoodRange 7 26 32 :=
  chunk_sound 7 _ _ 26 row7_26 check7_26

private def row7_32 : List Row := cert16Rows% "../Data/N07.bin" 114972 6
private theorem check7_32 : checkChunk 7 (table 7) (table 8) 32 row7_32 = true := by decide +kernel
private theorem good7_32 : GoodRange 7 32 38 :=
  chunk_sound 7 _ _ 32 row7_32 check7_32

private def row7_38 : List Row := cert16Rows% "../Data/N07.bin" 135068 6
private theorem check7_38 : checkChunk 7 (table 7) (table 8) 38 row7_38 = true := by decide +kernel
private theorem good7_38 : GoodRange 7 38 44 :=
  chunk_sound 7 _ _ 38 row7_38 check7_38

private def row7_44 : List Row := cert16Rows% "../Data/N07.bin" 155752 7
private theorem check7_44 : checkChunk 7 (table 7) (table 8) 44 row7_44 = true := by decide +kernel
private theorem good7_44 : GoodRange 7 44 51 :=
  chunk_sound 7 _ _ 44 row7_44 check7_44

private def row7_51 : List Row := cert16Rows% "../Data/N07.bin" 174918 7
private theorem check7_51 : checkChunk 7 (table 7) (table 8) 51 row7_51 = true := by decide +kernel
private theorem good7_51 : GoodRange 7 51 58 :=
  chunk_sound 7 _ _ 51 row7_51 check7_51

private def row7_58 : List Row := cert16Rows% "../Data/N07.bin" 194784 5
private theorem check7_58 : checkChunk 7 (table 7) (table 8) 58 row7_58 = true := by decide +kernel
private theorem good7_58 : GoodRange 7 58 63 :=
  chunk_sound 7 _ _ 58 row7_58 check7_58

private def row7_63 : List Row := cert16Rows% "../Data/N07.bin" 212814 6
private theorem check7_63 : checkChunk 7 (table 7) (table 8) 63 row7_63 = true := by decide +kernel
private theorem good7_63 : GoodRange 7 63 69 :=
  chunk_sound 7 _ _ 63 row7_63 check7_63

private def row7_69 : List Row := cert16Rows% "../Data/N07.bin" 233890 6
private theorem check7_69 : checkChunk 7 (table 7) (table 8) 69 row7_69 = true := by decide +kernel
private theorem good7_69 : GoodRange 7 69 75 :=
  chunk_sound 7 _ _ 69 row7_69 check7_69

theorem range7_0 : GoodRange 7 0 75 :=
  (joinRanges (joinRanges (joinRanges good7_0 (joinRanges good7_5 good7_10)) (joinRanges good7_15 (joinRanges good7_21 good7_26))) (joinRanges (joinRanges good7_32 (joinRanges good7_38 good7_44)) (joinRanges (joinRanges good7_51 good7_58) (joinRanges good7_63 good7_69))))

end Ramsey556.Cert16
