import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N11

-- Generated from N12.bin, SHA-256 60541557e97dd9a8baed389e06d9d7e133c64c9e89503f0f191a5dd47ec8e03b.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row12_235 : List Row := cert16Rows% "../Data/N12.bin" 72614 8
private theorem check12_235 : checkChunk 12 (table 12) (table 13) 235 row12_235 = true := by decide +kernel
private theorem good12_235 : GoodRange 12 235 243 :=
  chunk_sound 12 _ _ 235 row12_235 check12_235

private noncomputable def row12_243 : List Row := cert16Rows% "../Data/N12.bin" 74710 8
private theorem check12_243 : checkChunk 12 (table 12) (table 13) 243 row12_243 = true := by decide +kernel
private theorem good12_243 : GoodRange 12 243 251 :=
  chunk_sound 12 _ _ 243 row12_243 check12_243

private noncomputable def row12_251 : List Row := cert16Rows% "../Data/N12.bin" 76930 8
private theorem check12_251 : checkChunk 12 (table 12) (table 13) 251 row12_251 = true := by decide +kernel
private theorem good12_251 : GoodRange 12 251 259 :=
  chunk_sound 12 _ _ 251 row12_251 check12_251

private noncomputable def row12_259 : List Row := cert16Rows% "../Data/N12.bin" 79070 8
private theorem check12_259 : checkChunk 12 (table 12) (table 13) 259 row12_259 = true := by decide +kernel
private theorem good12_259 : GoodRange 12 259 267 :=
  chunk_sound 12 _ _ 259 row12_259 check12_259

private noncomputable def row12_267 : List Row := cert16Rows% "../Data/N12.bin" 81166 8
private theorem check12_267 : checkChunk 12 (table 12) (table 13) 267 row12_267 = true := by decide +kernel
private theorem good12_267 : GoodRange 12 267 275 :=
  chunk_sound 12 _ _ 267 row12_267 check12_267

private noncomputable def row12_275 : List Row := cert16Rows% "../Data/N12.bin" 83262 8
private theorem check12_275 : checkChunk 12 (table 12) (table 13) 275 row12_275 = true := by decide +kernel
private theorem good12_275 : GoodRange 12 275 283 :=
  chunk_sound 12 _ _ 275 row12_275 check12_275

private noncomputable def row12_283 : List Row := cert16Rows% "../Data/N12.bin" 85386 8
private theorem check12_283 : checkChunk 12 (table 12) (table 13) 283 row12_283 = true := by decide +kernel
private theorem good12_283 : GoodRange 12 283 291 :=
  chunk_sound 12 _ _ 283 row12_283 check12_283

private noncomputable def row12_291 : List Row := cert16Rows% "../Data/N12.bin" 87482 8
private theorem check12_291 : checkChunk 12 (table 12) (table 13) 291 row12_291 = true := by decide +kernel
private theorem good12_291 : GoodRange 12 291 299 :=
  chunk_sound 12 _ _ 291 row12_291 check12_291

private noncomputable def row12_299 : List Row := cert16Rows% "../Data/N12.bin" 89606 8
private theorem check12_299 : checkChunk 12 (table 12) (table 13) 299 row12_299 = true := by decide +kernel
private theorem good12_299 : GoodRange 12 299 307 :=
  chunk_sound 12 _ _ 299 row12_299 check12_299

private noncomputable def row12_307 : List Row := cert16Rows% "../Data/N12.bin" 91702 7
private theorem check12_307 : checkChunk 12 (table 12) (table 13) 307 row12_307 = true := by decide +kernel
private theorem good12_307 : GoodRange 12 307 314 :=
  chunk_sound 12 _ _ 307 row12_307 check12_307

private noncomputable def row12_314 : List Row := cert16Rows% "../Data/N12.bin" 94672 2
private theorem check12_314 : checkChunk 12 (table 12) (table 13) 314 row12_314 = true := by decide +kernel
private theorem good12_314 : GoodRange 12 314 316 :=
  chunk_sound 12 _ _ 314 row12_314 check12_314

private noncomputable def row12_316 : List Row := cert16Rows% "../Data/N12.bin" 96232 3
private theorem check12_316 : checkChunk 12 (table 12) (table 13) 316 row12_316 = true := by decide +kernel
private theorem good12_316 : GoodRange 12 316 319 :=
  chunk_sound 12 _ _ 316 row12_316 check12_316

theorem range12_3 : GoodRange 12 235 319 :=
  (joinRanges (joinRanges (joinRanges good12_235 (joinRanges good12_243 good12_251)) (joinRanges good12_259 (joinRanges good12_267 good12_275))) (joinRanges (joinRanges good12_283 (joinRanges good12_291 good12_299)) (joinRanges good12_307 (joinRanges good12_314 good12_316))))

end Ramsey556.Cert16
