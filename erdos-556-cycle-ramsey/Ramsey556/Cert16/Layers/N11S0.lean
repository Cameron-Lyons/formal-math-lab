import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N10

-- Generated from N11.bin, SHA-256 c734b5815c1d5d7aa1eed846b5438b32e3eb0e937dcbb95e79e92606ef30c2f6.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row11_0 : List Row := cert16Rows% "../Data/N11.bin" 0 3
private theorem check11_0 : checkChunk 11 (table 11) (table 12) 0 row11_0 = true := by decide +kernel
private theorem good11_0 : GoodRange 11 0 3 :=
  chunk_sound 11 _ _ 0 row11_0 check11_0

private noncomputable def row11_3 : List Row := cert16Rows% "../Data/N11.bin" 2530 5
private theorem check11_3 : checkChunk 11 (table 11) (table 12) 3 row11_3 = true := by decide +kernel
private theorem good11_3 : GoodRange 11 3 8 :=
  chunk_sound 11 _ _ 3 row11_3 check11_3

private noncomputable def row11_8 : List Row := cert16Rows% "../Data/N11.bin" 4804 6
private theorem check11_8 : checkChunk 11 (table 11) (table 12) 8 row11_8 = true := by decide +kernel
private theorem good11_8 : GoodRange 11 8 14 :=
  chunk_sound 11 _ _ 8 row11_8 check11_8

private noncomputable def row11_14 : List Row := cert16Rows% "../Data/N11.bin" 6980 7
private theorem check11_14 : checkChunk 11 (table 11) (table 12) 14 row11_14 = true := by decide +kernel
private theorem good11_14 : GoodRange 11 14 21 :=
  chunk_sound 11 _ _ 14 row11_14 check11_14

private noncomputable def row11_21 : List Row := cert16Rows% "../Data/N11.bin" 9350 5
private theorem check11_21 : checkChunk 11 (table 11) (table 12) 21 row11_21 = true := by decide +kernel
private theorem good11_21 : GoodRange 11 21 26 :=
  chunk_sound 11 _ _ 21 row11_21 check11_21

private noncomputable def row11_26 : List Row := cert16Rows% "../Data/N11.bin" 11392 6
private theorem check11_26 : checkChunk 11 (table 11) (table 12) 26 row11_26 = true := by decide +kernel
private theorem good11_26 : GoodRange 11 26 32 :=
  chunk_sound 11 _ _ 26 row11_26 check11_26

private noncomputable def row11_32 : List Row := cert16Rows% "../Data/N11.bin" 13360 8
private theorem check11_32 : checkChunk 11 (table 11) (table 12) 32 row11_32 = true := by decide +kernel
private theorem good11_32 : GoodRange 11 32 40 :=
  chunk_sound 11 _ _ 32 row11_32 check11_32

private noncomputable def row11_40 : List Row := cert16Rows% "../Data/N11.bin" 15476 10
private theorem check11_40 : checkChunk 11 (table 11) (table 12) 40 row11_40 = true := by decide +kernel
private theorem good11_40 : GoodRange 11 40 50 :=
  chunk_sound 11 _ _ 40 row11_40 check11_40

private noncomputable def row11_50 : List Row := cert16Rows% "../Data/N11.bin" 17644 3
private theorem check11_50 : checkChunk 11 (table 11) (table 12) 50 row11_50 = true := by decide +kernel
private theorem good11_50 : GoodRange 11 50 53 :=
  chunk_sound 11 _ _ 50 row11_50 check11_50

private noncomputable def row11_53 : List Row := cert16Rows% "../Data/N11.bin" 19530 7
private theorem check11_53 : checkChunk 11 (table 11) (table 12) 53 row11_53 = true := by decide +kernel
private theorem good11_53 : GoodRange 11 53 60 :=
  chunk_sound 11 _ _ 53 row11_53 check11_53

private noncomputable def row11_60 : List Row := cert16Rows% "../Data/N11.bin" 21688 9
private theorem check11_60 : checkChunk 11 (table 11) (table 12) 60 row11_60 = true := by decide +kernel
private theorem good11_60 : GoodRange 11 60 69 :=
  chunk_sound 11 _ _ 60 row11_60 check11_60

private noncomputable def row11_69 : List Row := cert16Rows% "../Data/N11.bin" 23734 8
private theorem check11_69 : checkChunk 11 (table 11) (table 12) 69 row11_69 = true := by decide +kernel
private theorem good11_69 : GoodRange 11 69 77 :=
  chunk_sound 11 _ _ 69 row11_69 check11_69

private noncomputable def row11_77 : List Row := cert16Rows% "../Data/N11.bin" 25986 9
private theorem check11_77 : checkChunk 11 (table 11) (table 12) 77 row11_77 = true := by decide +kernel
private theorem good11_77 : GoodRange 11 77 86 :=
  chunk_sound 11 _ _ 77 row11_77 check11_77

private noncomputable def row11_86 : List Row := cert16Rows% "../Data/N11.bin" 28048 7
private theorem check11_86 : checkChunk 11 (table 11) (table 12) 86 row11_86 = true := by decide +kernel
private theorem good11_86 : GoodRange 11 86 93 :=
  chunk_sound 11 _ _ 86 row11_86 check11_86

private noncomputable def row11_93 : List Row := cert16Rows% "../Data/N11.bin" 30198 10
private theorem check11_93 : checkChunk 11 (table 11) (table 12) 93 row11_93 = true := by decide +kernel
private theorem good11_93 : GoodRange 11 93 103 :=
  chunk_sound 11 _ _ 93 row11_93 check11_93

private noncomputable def row11_103 : List Row := cert16Rows% "../Data/N11.bin" 32466 9
private theorem check11_103 : checkChunk 11 (table 11) (table 12) 103 row11_103 = true := by decide +kernel
private theorem good11_103 : GoodRange 11 103 112 :=
  chunk_sound 11 _ _ 103 row11_103 check11_103

private noncomputable def row11_112 : List Row := cert16Rows% "../Data/N11.bin" 34792 8
private theorem check11_112 : checkChunk 11 (table 11) (table 12) 112 row11_112 = true := by decide +kernel
private theorem good11_112 : GoodRange 11 112 120 :=
  chunk_sound 11 _ _ 112 row11_112 check11_112

private noncomputable def row11_120 : List Row := cert16Rows% "../Data/N11.bin" 36868 9
private theorem check11_120 : checkChunk 11 (table 11) (table 12) 120 row11_120 = true := by decide +kernel
private theorem good11_120 : GoodRange 11 120 129 :=
  chunk_sound 11 _ _ 120 row11_120 check11_120

private noncomputable def row11_129 : List Row := cert16Rows% "../Data/N11.bin" 38926 10
private theorem check11_129 : checkChunk 11 (table 11) (table 12) 129 row11_129 = true := by decide +kernel
private theorem good11_129 : GoodRange 11 129 139 :=
  chunk_sound 11 _ _ 129 row11_129 check11_129

private noncomputable def row11_139 : List Row := cert16Rows% "../Data/N11.bin" 41182 9
private theorem check11_139 : checkChunk 11 (table 11) (table 12) 139 row11_139 = true := by decide +kernel
private theorem good11_139 : GoodRange 11 139 148 :=
  chunk_sound 11 _ _ 139 row11_139 check11_139

private noncomputable def row11_148 : List Row := cert16Rows% "../Data/N11.bin" 43284 9
private theorem check11_148 : checkChunk 11 (table 11) (table 12) 148 row11_148 = true := by decide +kernel
private theorem good11_148 : GoodRange 11 148 157 :=
  chunk_sound 11 _ _ 148 row11_148 check11_148

private noncomputable def row11_157 : List Row := cert16Rows% "../Data/N11.bin" 45458 9
private theorem check11_157 : checkChunk 11 (table 11) (table 12) 157 row11_157 = true := by decide +kernel
private theorem good11_157 : GoodRange 11 157 166 :=
  chunk_sound 11 _ _ 157 row11_157 check11_157

private noncomputable def row11_166 : List Row := cert16Rows% "../Data/N11.bin" 47640 10
private theorem check11_166 : checkChunk 11 (table 11) (table 12) 166 row11_166 = true := by decide +kernel
private theorem good11_166 : GoodRange 11 166 176 :=
  chunk_sound 11 _ _ 166 row11_166 check11_166

private noncomputable def row11_176 : List Row := cert16Rows% "../Data/N11.bin" 49856 4
private theorem check11_176 : checkChunk 11 (table 11) (table 12) 176 row11_176 = true := by decide +kernel
private theorem good11_176 : GoodRange 11 176 180 :=
  chunk_sound 11 _ _ 176 row11_176 check11_176

private noncomputable def row11_180 : List Row := cert16Rows% "../Data/N11.bin" 53864 1
private theorem check11_180 : checkChunk 11 (table 11) (table 12) 180 row11_180 = true := by decide +kernel
private theorem good11_180 : GoodRange 11 180 181 :=
  chunk_sound 11 _ _ 180 row11_180 check11_180

theorem range11_0 : GoodRange 11 0 181 :=
  (joinRanges (joinRanges (joinRanges (joinRanges good11_0 (joinRanges good11_3 good11_8)) (joinRanges good11_14 (joinRanges good11_21 good11_26))) (joinRanges (joinRanges good11_32 (joinRanges good11_40 good11_50)) (joinRanges good11_53 (joinRanges good11_60 good11_69)))) (joinRanges (joinRanges (joinRanges good11_77 (joinRanges good11_86 good11_93)) (joinRanges good11_103 (joinRanges good11_112 good11_120))) (joinRanges (joinRanges good11_129 (joinRanges good11_139 good11_148)) (joinRanges (joinRanges good11_157 good11_166) (joinRanges good11_176 good11_180)))))

end Ramsey556.Cert16
