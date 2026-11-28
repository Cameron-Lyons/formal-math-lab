import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N06

-- Generated from N07.bin, SHA-256 b53b70c2f56a30aa7049c83809718dd1441ae04b2f5bd5669e1a6117dc25cd21.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private def row7_262 : List Row := cert16Rows% "../Data/N07.bin" 766664 7
private theorem check7_262 : checkChunk 7 (table 7) (table 8) 262 row7_262 = true := by decide +kernel
private theorem good7_262 : GoodRange 7 262 269 :=
  chunk_sound 7 _ _ 262 row7_262 check7_262

private def row7_269 : List Row := cert16Rows% "../Data/N07.bin" 786810 7
private theorem check7_269 : checkChunk 7 (table 7) (table 8) 269 row7_269 = true := by decide +kernel
private theorem good7_269 : GoodRange 7 269 276 :=
  chunk_sound 7 _ _ 269 row7_269 check7_269

private def row7_276 : List Row := cert16Rows% "../Data/N07.bin" 805388 6
private theorem check7_276 : checkChunk 7 (table 7) (table 8) 276 row7_276 = true := by decide +kernel
private theorem good7_276 : GoodRange 7 276 282 :=
  chunk_sound 7 _ _ 276 row7_276 check7_276

private def row7_282 : List Row := cert16Rows% "../Data/N07.bin" 823916 9
private theorem check7_282 : checkChunk 7 (table 7) (table 8) 282 row7_282 = true := by decide +kernel
private theorem good7_282 : GoodRange 7 282 291 :=
  chunk_sound 7 _ _ 282 row7_282 check7_282

private def row7_291 : List Row := cert16Rows% "../Data/N07.bin" 843182 9
private theorem check7_291 : checkChunk 7 (table 7) (table 8) 291 row7_291 = true := by decide +kernel
private theorem good7_291 : GoodRange 7 291 300 :=
  chunk_sound 7 _ _ 291 row7_291 check7_291

private def row7_300 : List Row := cert16Rows% "../Data/N07.bin" 861468 10
private theorem check7_300 : checkChunk 7 (table 7) (table 8) 300 row7_300 = true := by decide +kernel
private theorem good7_300 : GoodRange 7 300 310 :=
  chunk_sound 7 _ _ 300 row7_300 check7_300

private def row7_310 : List Row := cert16Rows% "../Data/N07.bin" 880588 8
private theorem check7_310 : checkChunk 7 (table 7) (table 8) 310 row7_310 = true := by decide +kernel
private theorem good7_310 : GoodRange 7 310 318 :=
  chunk_sound 7 _ _ 310 row7_310 check7_310

private def row7_318 : List Row := cert16Rows% "../Data/N07.bin" 899608 7
private theorem check7_318 : checkChunk 7 (table 7) (table 8) 318 row7_318 = true := by decide +kernel
private theorem good7_318 : GoodRange 7 318 325 :=
  chunk_sound 7 _ _ 318 row7_318 check7_318

private def row7_325 : List Row := cert16Rows% "../Data/N07.bin" 918186 10
private theorem check7_325 : checkChunk 7 (table 7) (table 8) 325 row7_325 = true := by decide +kernel
private theorem good7_325 : GoodRange 7 325 335 :=
  chunk_sound 7 _ _ 325 row7_325 check7_325

private def row7_335 : List Row := cert16Rows% "../Data/N07.bin" 938286 9
private theorem check7_335 : checkChunk 7 (table 7) (table 8) 335 row7_335 = true := by decide +kernel
private theorem good7_335 : GoodRange 7 335 344 :=
  chunk_sound 7 _ _ 335 row7_335 check7_335

private def row7_344 : List Row := cert16Rows% "../Data/N07.bin" 957552 10
private theorem check7_344 : checkChunk 7 (table 7) (table 8) 344 row7_344 = true := by decide +kernel
private theorem good7_344 : GoodRange 7 344 354 :=
  chunk_sound 7 _ _ 344 row7_344 check7_344

private def row7_354 : List Row := cert16Rows% "../Data/N07.bin" 976672 8
private theorem check7_354 : checkChunk 7 (table 7) (table 8) 354 row7_354 = true := by decide +kernel
private theorem good7_354 : GoodRange 7 354 362 :=
  chunk_sound 7 _ _ 354 row7_354 check7_354

private def row7_362 : List Row := cert16Rows% "../Data/N07.bin" 995692 9
private theorem check7_362 : checkChunk 7 (table 7) (table 8) 362 row7_362 = true := by decide +kernel
private theorem good7_362 : GoodRange 7 362 371 :=
  chunk_sound 7 _ _ 362 row7_362 check7_362

private def row7_371 : List Row := cert16Rows% "../Data/N07.bin" 1013978 3
private theorem check7_371 : checkChunk 7 (table 7) (table 8) 371 row7_371 = true := by decide +kernel
private theorem good7_371 : GoodRange 7 371 374 :=
  chunk_sound 7 _ _ 371 row7_371 check7_371

theorem range7_3 : GoodRange 7 262 374 :=
  (joinRanges (joinRanges (joinRanges good7_262 (joinRanges good7_269 good7_276)) (joinRanges (joinRanges good7_282 good7_291) (joinRanges good7_300 good7_310))) (joinRanges (joinRanges good7_318 (joinRanges good7_325 good7_335)) (joinRanges (joinRanges good7_344 good7_354) (joinRanges good7_362 good7_371))))

end Ramsey556.Cert16
