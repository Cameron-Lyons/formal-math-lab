import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N11

-- Generated from N12.bin, SHA-256 60541557e97dd9a8baed389e06d9d7e133c64c9e89503f0f191a5dd47ec8e03b.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row12_72 : List Row := cert16Rows% "../Data/N12.bin" 22264 9
private theorem check12_72 : checkChunk 12 (table 12) (table 13) 72 row12_72 = true := by decide +kernel
private theorem good12_72 : GoodRange 12 72 81 :=
  chunk_sound 12 _ _ 72 row12_72 check12_72

private noncomputable def row12_81 : List Row := cert16Rows% "../Data/N12.bin" 24506 8
private theorem check12_81 : checkChunk 12 (table 12) (table 13) 81 row12_81 = true := by decide +kernel
private theorem good12_81 : GoodRange 12 81 89 :=
  chunk_sound 12 _ _ 81 row12_81 check12_81

private noncomputable def row12_89 : List Row := cert16Rows% "../Data/N12.bin" 26698 8
private theorem check12_89 : checkChunk 12 (table 12) (table 13) 89 row12_89 = true := by decide +kernel
private theorem good12_89 : GoodRange 12 89 97 :=
  chunk_sound 12 _ _ 89 row12_89 check12_89

private noncomputable def row12_97 : List Row := cert16Rows% "../Data/N12.bin" 28890 8
private theorem check12_97 : checkChunk 12 (table 12) (table 13) 97 row12_97 = true := by decide +kernel
private theorem good12_97 : GoodRange 12 97 105 :=
  chunk_sound 12 _ _ 97 row12_97 check12_97

private noncomputable def row12_105 : List Row := cert16Rows% "../Data/N12.bin" 31082 9
private theorem check12_105 : checkChunk 12 (table 12) (table 13) 105 row12_105 = true := by decide +kernel
private theorem good12_105 : GoodRange 12 105 114 :=
  chunk_sound 12 _ _ 105 row12_105 check12_105

private noncomputable def row12_114 : List Row := cert16Rows% "../Data/N12.bin" 33324 1
private theorem check12_114 : checkChunk 12 (table 12) (table 13) 114 row12_114 = true := by decide +kernel
private theorem good12_114 : GoodRange 12 114 115 :=
  chunk_sound 12 _ _ 114 row12_114 check12_114

private noncomputable def row12_115 : List Row := cert16Rows% "../Data/N12.bin" 35874 2
private theorem check12_115 : checkChunk 12 (table 12) (table 13) 115 row12_115 = true := by decide +kernel
private theorem good12_115 : GoodRange 12 115 117 :=
  chunk_sound 12 _ _ 115 row12_115 check12_115

private noncomputable def row12_117 : List Row := cert16Rows% "../Data/N12.bin" 38174 6
private theorem check12_117 : checkChunk 12 (table 12) (table 13) 117 row12_117 = true := by decide +kernel
private theorem good12_117 : GoodRange 12 117 123 :=
  chunk_sound 12 _ _ 117 row12_117 check12_117

private noncomputable def row12_123 : List Row := cert16Rows% "../Data/N12.bin" 40002 5
private theorem check12_123 : checkChunk 12 (table 12) (table 13) 123 row12_123 = true := by decide +kernel
private theorem good12_123 : GoodRange 12 123 128 :=
  chunk_sound 12 _ _ 123 row12_123 check12_123

private noncomputable def row12_128 : List Row := cert16Rows% "../Data/N12.bin" 41872 8
private theorem check12_128 : checkChunk 12 (table 12) (table 13) 128 row12_128 = true := by decide +kernel
private theorem good12_128 : GoodRange 12 128 136 :=
  chunk_sound 12 _ _ 128 row12_128 check12_128

private noncomputable def row12_136 : List Row := cert16Rows% "../Data/N12.bin" 44064 9
private theorem check12_136 : checkChunk 12 (table 12) (table 13) 136 row12_136 = true := by decide +kernel
private theorem good12_136 : GoodRange 12 136 145 :=
  chunk_sound 12 _ _ 136 row12_136 check12_136

private noncomputable def row12_145 : List Row := cert16Rows% "../Data/N12.bin" 46334 8
private theorem check12_145 : checkChunk 12 (table 12) (table 13) 145 row12_145 = true := by decide +kernel
private theorem good12_145 : GoodRange 12 145 153 :=
  chunk_sound 12 _ _ 145 row12_145 check12_145

theorem range12_1 : GoodRange 12 72 153 :=
  (joinRanges (joinRanges (joinRanges good12_72 (joinRanges good12_81 good12_89)) (joinRanges good12_97 (joinRanges good12_105 good12_114))) (joinRanges (joinRanges good12_115 (joinRanges good12_117 good12_123)) (joinRanges good12_128 (joinRanges good12_136 good12_145))))

end Ramsey556.Cert16
