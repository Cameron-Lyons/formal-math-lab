import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N11

-- Generated from N12.bin, SHA-256 60541557e97dd9a8baed389e06d9d7e133c64c9e89503f0f191a5dd47ec8e03b.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row12_153 : List Row := cert16Rows% "../Data/N12.bin" 48386 8
private theorem check12_153 : checkChunk 12 (table 12) (table 13) 153 row12_153 = true := by decide +kernel
private theorem good12_153 : GoodRange 12 153 161 :=
  chunk_sound 12 _ _ 153 row12_153 check12_153

private noncomputable def row12_161 : List Row := cert16Rows% "../Data/N12.bin" 50438 9
private theorem check12_161 : checkChunk 12 (table 12) (table 13) 161 row12_161 = true := by decide +kernel
private theorem good12_161 : GoodRange 12 161 170 :=
  chunk_sound 12 _ _ 161 row12_161 check12_161

private noncomputable def row12_170 : List Row := cert16Rows% "../Data/N12.bin" 52708 7
private theorem check12_170 : checkChunk 12 (table 12) (table 13) 170 row12_170 = true := by decide +kernel
private theorem good12_170 : GoodRange 12 170 177 :=
  chunk_sound 12 _ _ 170 row12_170 check12_170

private noncomputable def row12_177 : List Row := cert16Rows% "../Data/N12.bin" 54726 7
private theorem check12_177 : checkChunk 12 (table 12) (table 13) 177 row12_177 = true := by decide +kernel
private theorem good12_177 : GoodRange 12 177 184 :=
  chunk_sound 12 _ _ 177 row12_177 check12_177

private noncomputable def row12_184 : List Row := cert16Rows% "../Data/N12.bin" 56744 9
private theorem check12_184 : checkChunk 12 (table 12) (table 13) 184 row12_184 = true := by decide +kernel
private theorem good12_184 : GoodRange 12 184 193 :=
  chunk_sound 12 _ _ 184 row12_184 check12_184

private noncomputable def row12_193 : List Row := cert16Rows% "../Data/N12.bin" 58958 3
private theorem check12_193 : checkChunk 12 (table 12) (table 13) 193 row12_193 = true := by decide +kernel
private theorem good12_193 : GoodRange 12 193 196 :=
  chunk_sound 12 _ _ 193 row12_193 check12_193

private noncomputable def row12_196 : List Row := cert16Rows% "../Data/N12.bin" 60600 2
private theorem check12_196 : checkChunk 12 (table 12) (table 13) 196 row12_196 = true := by decide +kernel
private theorem good12_196 : GoodRange 12 196 198 :=
  chunk_sound 12 _ _ 196 row12_196 check12_196

private noncomputable def row12_198 : List Row := cert16Rows% "../Data/N12.bin" 62144 5
private theorem check12_198 : checkChunk 12 (table 12) (table 13) 198 row12_198 = true := by decide +kernel
private theorem good12_198 : GoodRange 12 198 203 :=
  chunk_sound 12 _ _ 198 row12_198 check12_198

private noncomputable def row12_203 : List Row := cert16Rows% "../Data/N12.bin" 63994 9
private theorem check12_203 : checkChunk 12 (table 12) (table 13) 203 row12_203 = true := by decide +kernel
private theorem good12_203 : GoodRange 12 203 212 :=
  chunk_sound 12 _ _ 203 row12_203 check12_203

private noncomputable def row12_212 : List Row := cert16Rows% "../Data/N12.bin" 66236 8
private theorem check12_212 : checkChunk 12 (table 12) (table 13) 212 row12_212 = true := by decide +kernel
private theorem good12_212 : GoodRange 12 212 220 :=
  chunk_sound 12 _ _ 212 row12_212 check12_212

private noncomputable def row12_220 : List Row := cert16Rows% "../Data/N12.bin" 68528 7
private theorem check12_220 : checkChunk 12 (table 12) (table 13) 220 row12_220 = true := by decide +kernel
private theorem good12_220 : GoodRange 12 220 227 :=
  chunk_sound 12 _ _ 220 row12_220 check12_220

private noncomputable def row12_227 : List Row := cert16Rows% "../Data/N12.bin" 70534 8
private theorem check12_227 : checkChunk 12 (table 12) (table 13) 227 row12_227 = true := by decide +kernel
private theorem good12_227 : GoodRange 12 227 235 :=
  chunk_sound 12 _ _ 227 row12_227 check12_227

theorem range12_2 : GoodRange 12 153 235 :=
  (joinRanges (joinRanges (joinRanges good12_153 (joinRanges good12_161 good12_170)) (joinRanges good12_177 (joinRanges good12_184 good12_193))) (joinRanges (joinRanges good12_196 (joinRanges good12_198 good12_203)) (joinRanges good12_212 (joinRanges good12_220 good12_227))))

end Ramsey556.Cert16
