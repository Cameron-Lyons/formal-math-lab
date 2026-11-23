import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N06

-- Generated from N07.bin, SHA-256 b53b70c2f56a30aa7049c83809718dd1441ae04b2f5bd5669e1a6117dc25cd21.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private def row7_166 : List Row := cert16Rows% "../Data/N07.bin" 517592 7
private theorem check7_166 : checkChunk 7 (table 7) (table 8) 166 row7_166 = true := by decide +kernel
private theorem good7_166 : GoodRange 7 166 173 :=
  chunk_sound 7 _ _ 166 row7_166 check7_166

private def row7_173 : List Row := cert16Rows% "../Data/N07.bin" 535778 6
private theorem check7_173 : checkChunk 7 (table 7) (table 8) 173 row7_173 = true := by decide +kernel
private theorem good7_173 : GoodRange 7 173 179 :=
  chunk_sound 7 _ _ 173 row7_173 check7_173

private def row7_179 : List Row := cert16Rows% "../Data/N07.bin" 556266 6
private theorem check7_179 : checkChunk 7 (table 7) (table 8) 179 row7_179 = true := by decide +kernel
private theorem good7_179 : GoodRange 7 179 185 :=
  chunk_sound 7 _ _ 179 row7_179 check7_179

private def row7_185 : List Row := cert16Rows% "../Data/N07.bin" 574794 7
private theorem check7_185 : checkChunk 7 (table 7) (table 8) 185 row7_185 = true := by decide +kernel
private theorem good7_185 : GoodRange 7 185 192 :=
  chunk_sound 7 _ _ 185 row7_185 check7_185

private def row7_192 : List Row := cert16Rows% "../Data/N07.bin" 593372 7
private theorem check7_192 : checkChunk 7 (table 7) (table 8) 192 row7_192 = true := by decide +kernel
private theorem good7_192 : GoodRange 7 192 199 :=
  chunk_sound 7 _ _ 192 row7_192 check7_192

private def row7_199 : List Row := cert16Rows% "../Data/N07.bin" 612538 7
private theorem check7_199 : checkChunk 7 (table 7) (table 8) 199 row7_199 = true := by decide +kernel
private theorem good7_199 : GoodRange 7 199 206 :=
  chunk_sound 7 _ _ 199 row7_199 check7_199

private def row7_206 : List Row := cert16Rows% "../Data/N07.bin" 633272 9
private theorem check7_206 : checkChunk 7 (table 7) (table 8) 206 row7_206 = true := by decide +kernel
private theorem good7_206 : GoodRange 7 206 215 :=
  chunk_sound 7 _ _ 206 row7_206 check7_206

private def row7_215 : List Row := cert16Rows% "../Data/N07.bin" 652538 9
private theorem check7_215 : checkChunk 7 (table 7) (table 8) 215 row7_215 = true := by decide +kernel
private theorem good7_215 : GoodRange 7 215 224 :=
  chunk_sound 7 _ _ 215 row7_215 check7_215

private def row7_224 : List Row := cert16Rows% "../Data/N07.bin" 671804 10
private theorem check7_224 : checkChunk 7 (table 7) (table 8) 224 row7_224 = true := by decide +kernel
private theorem good7_224 : GoodRange 7 224 234 :=
  chunk_sound 7 _ _ 224 row7_224 check7_224

private def row7_234 : List Row := cert16Rows% "../Data/N07.bin" 689944 10
private theorem check7_234 : checkChunk 7 (table 7) (table 8) 234 row7_234 = true := by decide +kernel
private theorem good7_234 : GoodRange 7 234 244 :=
  chunk_sound 7 _ _ 234 row7_234 check7_234

private def row7_244 : List Row := cert16Rows% "../Data/N07.bin" 708084 6
private theorem check7_244 : checkChunk 7 (table 7) (table 8) 244 row7_244 = true := by decide +kernel
private theorem good7_244 : GoodRange 7 244 250 :=
  chunk_sound 7 _ _ 244 row7_244 check7_244

private def row7_250 : List Row := cert16Rows% "../Data/N07.bin" 727648 6
private theorem check7_250 : checkChunk 7 (table 7) (table 8) 250 row7_250 = true := by decide +kernel
private theorem good7_250 : GoodRange 7 250 256 :=
  chunk_sound 7 _ _ 250 row7_250 check7_250

private def row7_256 : List Row := cert16Rows% "../Data/N07.bin" 746372 6
private theorem check7_256 : checkChunk 7 (table 7) (table 8) 256 row7_256 = true := by decide +kernel
private theorem good7_256 : GoodRange 7 256 262 :=
  chunk_sound 7 _ _ 256 row7_256 check7_256

theorem range7_2 : GoodRange 7 166 262 :=
  (joinRanges (joinRanges (joinRanges good7_166 (joinRanges good7_173 good7_179)) (joinRanges good7_185 (joinRanges good7_192 good7_199))) (joinRanges (joinRanges good7_206 (joinRanges good7_215 good7_224)) (joinRanges (joinRanges good7_234 good7_244) (joinRanges good7_250 good7_256))))

end Ramsey556.Cert16
