import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N09

-- Generated from N10.bin, SHA-256 7891955cd31732f08ded65772703dcdeb8e7fc2847fd4520bfb223cc7da63f54.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row10_0 : List Row := cert16Rows% "../Data/N10.bin" 0 4
private theorem check10_0 : checkChunk 10 (table 10) (table 11) 0 row10_0 = true := by decide +kernel
private theorem good10_0 : GoodRange 10 0 4 :=
  chunk_sound 10 _ _ 0 row10_0 check10_0

private noncomputable def row10_4 : List Row := cert16Rows% "../Data/N10.bin" 2388 3
private theorem check10_4 : checkChunk 10 (table 10) (table 11) 4 row10_4 = true := by decide +kernel
private theorem good10_4 : GoodRange 10 4 7 :=
  chunk_sound 10 _ _ 4 row10_4 check10_4

private noncomputable def row10_7 : List Row := cert16Rows% "../Data/N10.bin" 5422 4
private theorem check10_7 : checkChunk 10 (table 10) (table 11) 7 row10_7 = true := by decide +kernel
private theorem good10_7 : GoodRange 10 7 11 :=
  chunk_sound 10 _ _ 7 row10_7 check10_7

private noncomputable def row10_11 : List Row := cert16Rows% "../Data/N10.bin" 7810 4
private theorem check10_11 : checkChunk 10 (table 10) (table 11) 11 row10_11 = true := by decide +kernel
private theorem good10_11 : GoodRange 10 11 15 :=
  chunk_sound 10 _ _ 11 row10_11 check10_11

private noncomputable def row10_15 : List Row := cert16Rows% "../Data/N10.bin" 10338 4
private theorem check10_15 : checkChunk 10 (table 10) (table 11) 15 row10_15 = true := by decide +kernel
private theorem good10_15 : GoodRange 10 15 19 :=
  chunk_sound 10 _ _ 15 row10_15 check10_15

private noncomputable def row10_19 : List Row := cert16Rows% "../Data/N10.bin" 13370 4
private theorem check10_19 : checkChunk 10 (table 10) (table 11) 19 row10_19 = true := by decide +kernel
private theorem good10_19 : GoodRange 10 19 23 :=
  chunk_sound 10 _ _ 19 row10_19 check10_19

private noncomputable def row10_23 : List Row := cert16Rows% "../Data/N10.bin" 15978 4
private theorem check10_23 : checkChunk 10 (table 10) (table 11) 23 row10_23 = true := by decide +kernel
private theorem good10_23 : GoodRange 10 23 27 :=
  chunk_sound 10 _ _ 23 row10_23 check10_23

private noncomputable def row10_27 : List Row := cert16Rows% "../Data/N10.bin" 18170 4
private theorem check10_27 : checkChunk 10 (table 10) (table 11) 27 row10_27 = true := by decide +kernel
private theorem good10_27 : GoodRange 10 27 31 :=
  chunk_sound 10 _ _ 27 row10_27 check10_27

private noncomputable def row10_31 : List Row := cert16Rows% "../Data/N10.bin" 20362 4
private theorem check10_31 : checkChunk 10 (table 10) (table 11) 31 row10_31 = true := by decide +kernel
private theorem good10_31 : GoodRange 10 31 35 :=
  chunk_sound 10 _ _ 31 row10_31 check10_31

private noncomputable def row10_35 : List Row := cert16Rows% "../Data/N10.bin" 22586 4
private theorem check10_35 : checkChunk 10 (table 10) (table 11) 35 row10_35 = true := by decide +kernel
private theorem good10_35 : GoodRange 10 35 39 :=
  chunk_sound 10 _ _ 35 row10_35 check10_35

private noncomputable def row10_39 : List Row := cert16Rows% "../Data/N10.bin" 24778 6
private theorem check10_39 : checkChunk 10 (table 10) (table 11) 39 row10_39 = true := by decide +kernel
private theorem good10_39 : GoodRange 10 39 45 :=
  chunk_sound 10 _ _ 39 row10_39 check10_39

private noncomputable def row10_45 : List Row := cert16Rows% "../Data/N10.bin" 27038 7
private theorem check10_45 : checkChunk 10 (table 10) (table 11) 45 row10_45 = true := by decide +kernel
private theorem good10_45 : GoodRange 10 45 52 :=
  chunk_sound 10 _ _ 45 row10_45 check10_45

private noncomputable def row10_52 : List Row := cert16Rows% "../Data/N10.bin" 29164 9
private theorem check10_52 : checkChunk 10 (table 10) (table 11) 52 row10_52 = true := by decide +kernel
private theorem good10_52 : GoodRange 10 52 61 :=
  chunk_sound 10 _ _ 52 row10_52 check10_52

private noncomputable def row10_61 : List Row := cert16Rows% "../Data/N10.bin" 31386 10
private theorem check10_61 : checkChunk 10 (table 10) (table 11) 61 row10_61 = true := by decide +kernel
private theorem good10_61 : GoodRange 10 61 71 :=
  chunk_sound 10 _ _ 61 row10_61 check10_61

private noncomputable def row10_71 : List Row := cert16Rows% "../Data/N10.bin" 33550 12
private theorem check10_71 : checkChunk 10 (table 10) (table 11) 71 row10_71 = true := by decide +kernel
private theorem good10_71 : GoodRange 10 71 83 :=
  chunk_sound 10 _ _ 71 row10_71 check10_71

private noncomputable def row10_83 : List Row := cert16Rows% "../Data/N10.bin" 35770 12
private theorem check10_83 : checkChunk 10 (table 10) (table 11) 83 row10_83 = true := by decide +kernel
private theorem good10_83 : GoodRange 10 83 95 :=
  chunk_sound 10 _ _ 83 row10_83 check10_83

private noncomputable def row10_95 : List Row := cert16Rows% "../Data/N10.bin" 37962 4
private theorem check10_95 : checkChunk 10 (table 10) (table 11) 95 row10_95 = true := by decide +kernel
private theorem good10_95 : GoodRange 10 95 99 :=
  chunk_sound 10 _ _ 95 row10_95 check10_95

private noncomputable def row10_99 : List Row := cert16Rows% "../Data/N10.bin" 42202 1
private theorem check10_99 : checkChunk 10 (table 10) (table 11) 99 row10_99 = true := by decide +kernel
private theorem good10_99 : GoodRange 10 99 100 :=
  chunk_sound 10 _ _ 99 row10_99 check10_99

private noncomputable def row10_100 : List Row := cert16Rows% "../Data/N10.bin" 45208 1
private theorem check10_100 : checkChunk 10 (table 10) (table 11) 100 row10_100 = true := by decide +kernel
private theorem good10_100 : GoodRange 10 100 101 :=
  chunk_sound 10 _ _ 100 row10_100 check10_100

private noncomputable def row10_101 : List Row := cert16Rows% "../Data/N10.bin" 48214 3
private theorem check10_101 : checkChunk 10 (table 10) (table 11) 101 row10_101 = true := by decide +kernel
private theorem good10_101 : GoodRange 10 101 104 :=
  chunk_sound 10 _ _ 101 row10_101 check10_101

private noncomputable def row10_104 : List Row := cert16Rows% "../Data/N10.bin" 50556 2
private theorem check10_104 : checkChunk 10 (table 10) (table 11) 104 row10_104 = true := by decide +kernel
private theorem good10_104 : GoodRange 10 104 106 :=
  chunk_sound 10 _ _ 104 row10_104 check10_104

private noncomputable def row10_106 : List Row := cert16Rows% "../Data/N10.bin" 54364 1
private theorem check10_106 : checkChunk 10 (table 10) (table 11) 106 row10_106 = true := by decide +kernel
private theorem good10_106 : GoodRange 10 106 107 :=
  chunk_sound 10 _ _ 106 row10_106 check10_106

private noncomputable def row10_107 : List Row := cert16Rows% "../Data/N10.bin" 57038 2
private theorem check10_107 : checkChunk 10 (table 10) (table 11) 107 row10_107 = true := by decide +kernel
private theorem good10_107 : GoodRange 10 107 109 :=
  chunk_sound 10 _ _ 107 row10_107 check10_107

private noncomputable def row10_109 : List Row := cert16Rows% "../Data/N10.bin" 60866 3
private theorem check10_109 : checkChunk 10 (table 10) (table 11) 109 row10_109 = true := by decide +kernel
private theorem good10_109 : GoodRange 10 109 112 :=
  chunk_sound 10 _ _ 109 row10_109 check10_109

private noncomputable def row10_112 : List Row := cert16Rows% "../Data/N10.bin" 63584 3
private theorem check10_112 : checkChunk 10 (table 10) (table 11) 112 row10_112 = true := by decide +kernel
private theorem good10_112 : GoodRange 10 112 115 :=
  chunk_sound 10 _ _ 112 row10_112 check10_112

private noncomputable def row10_115 : List Row := cert16Rows% "../Data/N10.bin" 66318 2
private theorem check10_115 : checkChunk 10 (table 10) (table 11) 115 row10_115 = true := by decide +kernel
private theorem good10_115 : GoodRange 10 115 117 :=
  chunk_sound 10 _ _ 115 row10_115 check10_115

private noncomputable def row10_117 : List Row := cert16Rows% "../Data/N10.bin" 85122 4
private theorem check10_117 : checkChunk 10 (table 10) (table 11) 117 row10_117 = true := by decide +kernel
private theorem good10_117 : GoodRange 10 117 121 :=
  chunk_sound 10 _ _ 117 row10_117 check10_117

private noncomputable def row10_121 : List Row := cert16Rows% "../Data/N10.bin" 87426 4
private theorem check10_121 : checkChunk 10 (table 10) (table 11) 121 row10_121 = true := by decide +kernel
private theorem good10_121 : GoodRange 10 121 125 :=
  chunk_sound 10 _ _ 121 row10_121 check10_121

private noncomputable def row10_125 : List Row := cert16Rows% "../Data/N10.bin" 89566 4
private theorem check10_125 : checkChunk 10 (table 10) (table 11) 125 row10_125 = true := by decide +kernel
private theorem good10_125 : GoodRange 10 125 129 :=
  chunk_sound 10 _ _ 125 row10_125 check10_125

private noncomputable def row10_129 : List Row := cert16Rows% "../Data/N10.bin" 91730 4
private theorem check10_129 : checkChunk 10 (table 10) (table 11) 129 row10_129 = true := by decide +kernel
private theorem good10_129 : GoodRange 10 129 133 :=
  chunk_sound 10 _ _ 129 row10_129 check10_129

private noncomputable def row10_133 : List Row := cert16Rows% "../Data/N10.bin" 93806 7
private theorem check10_133 : checkChunk 10 (table 10) (table 11) 133 row10_133 = true := by decide +kernel
private theorem good10_133 : GoodRange 10 133 140 :=
  chunk_sound 10 _ _ 133 row10_133 check10_133

private noncomputable def row10_140 : List Row := cert16Rows% "../Data/N10.bin" 95932 7
private theorem check10_140 : checkChunk 10 (table 10) (table 11) 140 row10_140 = true := by decide +kernel
private theorem good10_140 : GoodRange 10 140 147 :=
  chunk_sound 10 _ _ 140 row10_140 check10_140

private noncomputable def row10_147 : List Row := cert16Rows% "../Data/N10.bin" 98058 7
private theorem check10_147 : checkChunk 10 (table 10) (table 11) 147 row10_147 = true := by decide +kernel
private theorem good10_147 : GoodRange 10 147 154 :=
  chunk_sound 10 _ _ 147 row10_147 check10_147

private noncomputable def row10_154 : List Row := cert16Rows% "../Data/N10.bin" 100176 7
private theorem check10_154 : checkChunk 10 (table 10) (table 11) 154 row10_154 = true := by decide +kernel
private theorem good10_154 : GoodRange 10 154 161 :=
  chunk_sound 10 _ _ 154 row10_154 check10_154

private noncomputable def row10_161 : List Row := cert16Rows% "../Data/N10.bin" 102354 7
private theorem check10_161 : checkChunk 10 (table 10) (table 11) 161 row10_161 = true := by decide +kernel
private theorem good10_161 : GoodRange 10 161 168 :=
  chunk_sound 10 _ _ 161 row10_161 check10_161

private noncomputable def row10_168 : List Row := cert16Rows% "../Data/N10.bin" 104480 7
private theorem check10_168 : checkChunk 10 (table 10) (table 11) 168 row10_168 = true := by decide +kernel
private theorem good10_168 : GoodRange 10 168 175 :=
  chunk_sound 10 _ _ 168 row10_168 check10_168

private noncomputable def row10_175 : List Row := cert16Rows% "../Data/N10.bin" 106606 7
private theorem check10_175 : checkChunk 10 (table 10) (table 11) 175 row10_175 = true := by decide +kernel
private theorem good10_175 : GoodRange 10 175 182 :=
  chunk_sound 10 _ _ 175 row10_175 check10_175

private noncomputable def row10_182 : List Row := cert16Rows% "../Data/N10.bin" 108724 7
private theorem check10_182 : checkChunk 10 (table 10) (table 11) 182 row10_182 = true := by decide +kernel
private theorem good10_182 : GoodRange 10 182 189 :=
  chunk_sound 10 _ _ 182 row10_182 check10_182

private noncomputable def row10_189 : List Row := cert16Rows% "../Data/N10.bin" 110850 9
private theorem check10_189 : checkChunk 10 (table 10) (table 11) 189 row10_189 = true := by decide +kernel
private theorem good10_189 : GoodRange 10 189 198 :=
  chunk_sound 10 _ _ 189 row10_189 check10_189

private noncomputable def row10_198 : List Row := cert16Rows% "../Data/N10.bin" 112928 10
private theorem check10_198 : checkChunk 10 (table 10) (table 11) 198 row10_198 = true := by decide +kernel
private theorem good10_198 : GoodRange 10 198 208 :=
  chunk_sound 10 _ _ 198 row10_198 check10_198

private noncomputable def row10_208 : List Row := cert16Rows% "../Data/N10.bin" 115040 11
private theorem check10_208 : checkChunk 10 (table 10) (table 11) 208 row10_208 = true := by decide +kernel
private theorem good10_208 : GoodRange 10 208 219 :=
  chunk_sound 10 _ _ 208 row10_208 check10_208

private noncomputable def row10_219 : List Row := cert16Rows% "../Data/N10.bin" 117298 11
private theorem check10_219 : checkChunk 10 (table 10) (table 11) 219 row10_219 = true := by decide +kernel
private theorem good10_219 : GoodRange 10 219 230 :=
  chunk_sound 10 _ _ 219 row10_219 check10_219

private noncomputable def row10_230 : List Row := cert16Rows% "../Data/N10.bin" 119528 10
private theorem check10_230 : checkChunk 10 (table 10) (table 11) 230 row10_230 = true := by decide +kernel
private theorem good10_230 : GoodRange 10 230 240 :=
  chunk_sound 10 _ _ 230 row10_230 check10_230

private noncomputable def row10_240 : List Row := cert16Rows% "../Data/N10.bin" 121724 10
private theorem check10_240 : checkChunk 10 (table 10) (table 11) 240 row10_240 = true := by decide +kernel
private theorem good10_240 : GoodRange 10 240 250 :=
  chunk_sound 10 _ _ 240 row10_240 check10_240

private noncomputable def row10_250 : List Row := cert16Rows% "../Data/N10.bin" 123812 11
private theorem check10_250 : checkChunk 10 (table 10) (table 11) 250 row10_250 = true := by decide +kernel
private theorem good10_250 : GoodRange 10 250 261 :=
  chunk_sound 10 _ _ 250 row10_250 check10_250

private noncomputable def row10_261 : List Row := cert16Rows% "../Data/N10.bin" 126050 10
private theorem check10_261 : checkChunk 10 (table 10) (table 11) 261 row10_261 = true := by decide +kernel
private theorem good10_261 : GoodRange 10 261 271 :=
  chunk_sound 10 _ _ 261 row10_261 check10_261

private noncomputable def row10_271 : List Row := cert16Rows% "../Data/N10.bin" 128138 11
private theorem check10_271 : checkChunk 10 (table 10) (table 11) 271 row10_271 = true := by decide +kernel
private theorem good10_271 : GoodRange 10 271 282 :=
  chunk_sound 10 _ _ 271 row10_271 check10_271

private noncomputable def row10_282 : List Row := cert16Rows% "../Data/N10.bin" 130260 11
private theorem check10_282 : checkChunk 10 (table 10) (table 11) 282 row10_282 = true := by decide +kernel
private theorem good10_282 : GoodRange 10 282 293 :=
  chunk_sound 10 _ _ 282 row10_282 check10_282

private noncomputable def row10_293 : List Row := cert16Rows% "../Data/N10.bin" 132366 11
private theorem check10_293 : checkChunk 10 (table 10) (table 11) 293 row10_293 = true := by decide +kernel
private theorem good10_293 : GoodRange 10 293 304 :=
  chunk_sound 10 _ _ 293 row10_293 check10_293

private noncomputable def row10_304 : List Row := cert16Rows% "../Data/N10.bin" 134480 12
private theorem check10_304 : checkChunk 10 (table 10) (table 11) 304 row10_304 = true := by decide +kernel
private theorem good10_304 : GoodRange 10 304 316 :=
  chunk_sound 10 _ _ 304 row10_304 check10_304

private noncomputable def row10_316 : List Row := cert16Rows% "../Data/N10.bin" 136684 11
private theorem check10_316 : checkChunk 10 (table 10) (table 11) 316 row10_316 = true := by decide +kernel
private theorem good10_316 : GoodRange 10 316 327 :=
  chunk_sound 10 _ _ 316 row10_316 check10_316

private noncomputable def row10_327 : List Row := cert16Rows% "../Data/N10.bin" 138822 12
private theorem check10_327 : checkChunk 10 (table 10) (table 11) 327 row10_327 = true := by decide +kernel
private theorem good10_327 : GoodRange 10 327 339 :=
  chunk_sound 10 _ _ 327 row10_327 check10_327

private noncomputable def row10_339 : List Row := cert16Rows% "../Data/N10.bin" 141058 11
private theorem check10_339 : checkChunk 10 (table 10) (table 11) 339 row10_339 = true := by decide +kernel
private theorem good10_339 : GoodRange 10 339 350 :=
  chunk_sound 10 _ _ 339 row10_339 check10_339

private noncomputable def row10_350 : List Row := cert16Rows% "../Data/N10.bin" 143160 11
private theorem check10_350 : checkChunk 10 (table 10) (table 11) 350 row10_350 = true := by decide +kernel
private theorem good10_350 : GoodRange 10 350 361 :=
  chunk_sound 10 _ _ 350 row10_350 check10_350

private noncomputable def row10_361 : List Row := cert16Rows% "../Data/N10.bin" 145274 12
private theorem check10_361 : checkChunk 10 (table 10) (table 11) 361 row10_361 = true := by decide +kernel
private theorem good10_361 : GoodRange 10 361 373 :=
  chunk_sound 10 _ _ 361 row10_361 check10_361

private noncomputable def row10_373 : List Row := cert16Rows% "../Data/N10.bin" 147458 12
private theorem check10_373 : checkChunk 10 (table 10) (table 11) 373 row10_373 = true := by decide +kernel
private theorem good10_373 : GoodRange 10 373 385 :=
  chunk_sound 10 _ _ 373 row10_373 check10_373

private noncomputable def row10_385 : List Row := cert16Rows% "../Data/N10.bin" 149718 11
private theorem check10_385 : checkChunk 10 (table 10) (table 11) 385 row10_385 = true := by decide +kernel
private theorem good10_385 : GoodRange 10 385 396 :=
  chunk_sound 10 _ _ 385 row10_385 check10_385

private noncomputable def row10_396 : List Row := cert16Rows% "../Data/N10.bin" 151816 12
private theorem check10_396 : checkChunk 10 (table 10) (table 11) 396 row10_396 = true := by decide +kernel
private theorem good10_396 : GoodRange 10 396 408 :=
  chunk_sound 10 _ _ 396 row10_396 check10_396

private noncomputable def row10_408 : List Row := cert16Rows% "../Data/N10.bin" 154040 12
private theorem check10_408 : checkChunk 10 (table 10) (table 11) 408 row10_408 = true := by decide +kernel
private theorem good10_408 : GoodRange 10 408 420 :=
  chunk_sound 10 _ _ 408 row10_408 check10_408

private noncomputable def row10_420 : List Row := cert16Rows% "../Data/N10.bin" 156300 12
private theorem check10_420 : checkChunk 10 (table 10) (table 11) 420 row10_420 = true := by decide +kernel
private theorem good10_420 : GoodRange 10 420 432 :=
  chunk_sound 10 _ _ 420 row10_420 check10_420

private noncomputable def row10_432 : List Row := cert16Rows% "../Data/N10.bin" 158560 2
private theorem check10_432 : checkChunk 10 (table 10) (table 11) 432 row10_432 = true := by decide +kernel
private theorem good10_432 : GoodRange 10 432 434 :=
  chunk_sound 10 _ _ 432 row10_432 check10_432

private noncomputable def row10_434 : List Row := cert16Rows% "../Data/N10.bin" 161756 2
private theorem check10_434 : checkChunk 10 (table 10) (table 11) 434 row10_434 = true := by decide +kernel
private theorem good10_434 : GoodRange 10 434 436 :=
  chunk_sound 10 _ _ 434 row10_434 check10_434

private noncomputable def row10_436 : List Row := cert16Rows% "../Data/N10.bin" 165584 6
private theorem check10_436 : checkChunk 10 (table 10) (table 11) 436 row10_436 = true := by decide +kernel
private theorem good10_436 : GoodRange 10 436 442 :=
  chunk_sound 10 _ _ 436 row10_436 check10_436

private noncomputable def row10_442 : List Row := cert16Rows% "../Data/N10.bin" 168140 3
private theorem check10_442 : checkChunk 10 (table 10) (table 11) 442 row10_442 = true := by decide +kernel
private theorem good10_442 : GoodRange 10 442 445 :=
  chunk_sound 10 _ _ 442 row10_442 check10_442

private noncomputable def row10_445 : List Row := cert16Rows% "../Data/N10.bin" 170874 2
private theorem check10_445 : checkChunk 10 (table 10) (table 11) 445 row10_445 = true := by decide +kernel
private theorem good10_445 : GoodRange 10 445 447 :=
  chunk_sound 10 _ _ 445 row10_445 check10_445

private noncomputable def row10_447 : List Row := cert16Rows% "../Data/N10.bin" 174786 2
private theorem check10_447 : checkChunk 10 (table 10) (table 11) 447 row10_447 = true := by decide +kernel
private theorem good10_447 : GoodRange 10 447 449 :=
  chunk_sound 10 _ _ 447 row10_447 check10_447

private noncomputable def row10_449 : List Row := cert16Rows% "../Data/N10.bin" 178614 7
private theorem check10_449 : checkChunk 10 (table 10) (table 11) 449 row10_449 = true := by decide +kernel
private theorem good10_449 : GoodRange 10 449 456 :=
  chunk_sound 10 _ _ 449 row10_449 check10_449

private noncomputable def row10_456 : List Row := cert16Rows% "../Data/N10.bin" 181364 3
private theorem check10_456 : checkChunk 10 (table 10) (table 11) 456 row10_456 = true := by decide +kernel
private theorem good10_456 : GoodRange 10 456 459 :=
  chunk_sound 10 _ _ 456 row10_456 check10_456

private noncomputable def row10_459 : List Row := cert16Rows% "../Data/N10.bin" 184090 7
private theorem check10_459 : checkChunk 10 (table 10) (table 11) 459 row10_459 = true := by decide +kernel
private theorem good10_459 : GoodRange 10 459 466 :=
  chunk_sound 10 _ _ 459 row10_459 check10_459

private noncomputable def row10_466 : List Row := cert16Rows% "../Data/N10.bin" 186316 11
private theorem check10_466 : checkChunk 10 (table 10) (table 11) 466 row10_466 = true := by decide +kernel
private theorem good10_466 : GoodRange 10 466 477 :=
  chunk_sound 10 _ _ 466 row10_466 check10_466

private noncomputable def row10_477 : List Row := cert16Rows% "../Data/N10.bin" 188578 11
private theorem check10_477 : checkChunk 10 (table 10) (table 11) 477 row10_477 = true := by decide +kernel
private theorem good10_477 : GoodRange 10 477 488 :=
  chunk_sound 10 _ _ 477 row10_477 check10_477

private noncomputable def row10_488 : List Row := cert16Rows% "../Data/N10.bin" 190912 10
private theorem check10_488 : checkChunk 10 (table 10) (table 11) 488 row10_488 = true := by decide +kernel
private theorem good10_488 : GoodRange 10 488 498 :=
  chunk_sound 10 _ _ 488 row10_488 check10_488

private noncomputable def row10_498 : List Row := cert16Rows% "../Data/N10.bin" 193000 11
private theorem check10_498 : checkChunk 10 (table 10) (table 11) 498 row10_498 = true := by decide +kernel
private theorem good10_498 : GoodRange 10 498 509 :=
  chunk_sound 10 _ _ 498 row10_498 check10_498

private noncomputable def row10_509 : List Row := cert16Rows% "../Data/N10.bin" 195238 10
private theorem check10_509 : checkChunk 10 (table 10) (table 11) 509 row10_509 = true := by decide +kernel
private theorem good10_509 : GoodRange 10 509 519 :=
  chunk_sound 10 _ _ 509 row10_509 check10_509

private noncomputable def row10_519 : List Row := cert16Rows% "../Data/N10.bin" 197350 12
private theorem check10_519 : checkChunk 10 (table 10) (table 11) 519 row10_519 = true := by decide +kernel
private theorem good10_519 : GoodRange 10 519 531 :=
  chunk_sound 10 _ _ 519 row10_519 check10_519

private noncomputable def row10_531 : List Row := cert16Rows% "../Data/N10.bin" 199530 11
private theorem check10_531 : checkChunk 10 (table 10) (table 11) 531 row10_531 = true := by decide +kernel
private theorem good10_531 : GoodRange 10 531 542 :=
  chunk_sound 10 _ _ 531 row10_531 check10_531

private noncomputable def row10_542 : List Row := cert16Rows% "../Data/N10.bin" 201644 11
private theorem check10_542 : checkChunk 10 (table 10) (table 11) 542 row10_542 = true := by decide +kernel
private theorem good10_542 : GoodRange 10 542 553 :=
  chunk_sound 10 _ _ 542 row10_542 check10_542

private noncomputable def row10_553 : List Row := cert16Rows% "../Data/N10.bin" 203750 12
private theorem check10_553 : checkChunk 10 (table 10) (table 11) 553 row10_553 = true := by decide +kernel
private theorem good10_553 : GoodRange 10 553 565 :=
  chunk_sound 10 _ _ 553 row10_553 check10_553

private noncomputable def row10_565 : List Row := cert16Rows% "../Data/N10.bin" 205986 11
private theorem check10_565 : checkChunk 10 (table 10) (table 11) 565 row10_565 = true := by decide +kernel
private theorem good10_565 : GoodRange 10 565 576 :=
  chunk_sound 10 _ _ 565 row10_565 check10_565

private noncomputable def row10_576 : List Row := cert16Rows% "../Data/N10.bin" 208068 11
private theorem check10_576 : checkChunk 10 (table 10) (table 11) 576 row10_576 = true := by decide +kernel
private theorem good10_576 : GoodRange 10 576 587 :=
  chunk_sound 10 _ _ 576 row10_576 check10_576

private noncomputable def row10_587 : List Row := cert16Rows% "../Data/N10.bin" 210210 11
private theorem check10_587 : checkChunk 10 (table 10) (table 11) 587 row10_587 = true := by decide +kernel
private theorem good10_587 : GoodRange 10 587 598 :=
  chunk_sound 10 _ _ 587 row10_587 check10_587

private noncomputable def row10_598 : List Row := cert16Rows% "../Data/N10.bin" 212288 12
private theorem check10_598 : checkChunk 10 (table 10) (table 11) 598 row10_598 = true := by decide +kernel
private theorem good10_598 : GoodRange 10 598 610 :=
  chunk_sound 10 _ _ 598 row10_598 check10_598

private noncomputable def row10_610 : List Row := cert16Rows% "../Data/N10.bin" 214544 11
private theorem check10_610 : checkChunk 10 (table 10) (table 11) 610 row10_610 = true := by decide +kernel
private theorem good10_610 : GoodRange 10 610 621 :=
  chunk_sound 10 _ _ 610 row10_610 check10_610

private noncomputable def row10_621 : List Row := cert16Rows% "../Data/N10.bin" 216658 12
private theorem check10_621 : checkChunk 10 (table 10) (table 11) 621 row10_621 = true := by decide +kernel
private theorem good10_621 : GoodRange 10 621 633 :=
  chunk_sound 10 _ _ 621 row10_621 check10_621

private noncomputable def row10_633 : List Row := cert16Rows% "../Data/N10.bin" 218902 11
private theorem check10_633 : checkChunk 10 (table 10) (table 11) 633 row10_633 = true := by decide +kernel
private theorem good10_633 : GoodRange 10 633 644 :=
  chunk_sound 10 _ _ 633 row10_633 check10_633

private noncomputable def row10_644 : List Row := cert16Rows% "../Data/N10.bin" 221004 12
private theorem check10_644 : checkChunk 10 (table 10) (table 11) 644 row10_644 = true := by decide +kernel
private theorem good10_644 : GoodRange 10 644 656 :=
  chunk_sound 10 _ _ 644 row10_644 check10_644

private noncomputable def row10_656 : List Row := cert16Rows% "../Data/N10.bin" 223248 11
private theorem check10_656 : checkChunk 10 (table 10) (table 11) 656 row10_656 = true := by decide +kernel
private theorem good10_656 : GoodRange 10 656 667 :=
  chunk_sound 10 _ _ 656 row10_656 check10_656

private noncomputable def row10_667 : List Row := cert16Rows% "../Data/N10.bin" 225354 12
private theorem check10_667 : checkChunk 10 (table 10) (table 11) 667 row10_667 = true := by decide +kernel
private theorem good10_667 : GoodRange 10 667 679 :=
  chunk_sound 10 _ _ 667 row10_667 check10_667

private noncomputable def row10_679 : List Row := cert16Rows% "../Data/N10.bin" 227594 11
private theorem check10_679 : checkChunk 10 (table 10) (table 11) 679 row10_679 = true := by decide +kernel
private theorem good10_679 : GoodRange 10 679 690 :=
  chunk_sound 10 _ _ 679 row10_679 check10_679

private noncomputable def row10_690 : List Row := cert16Rows% "../Data/N10.bin" 229696 12
private theorem check10_690 : checkChunk 10 (table 10) (table 11) 690 row10_690 = true := by decide +kernel
private theorem good10_690 : GoodRange 10 690 702 :=
  chunk_sound 10 _ _ 690 row10_690 check10_690

private noncomputable def row10_702 : List Row := cert16Rows% "../Data/N10.bin" 231912 11
private theorem check10_702 : checkChunk 10 (table 10) (table 11) 702 row10_702 = true := by decide +kernel
private theorem good10_702 : GoodRange 10 702 713 :=
  chunk_sound 10 _ _ 702 row10_702 check10_702

private noncomputable def row10_713 : List Row := cert16Rows% "../Data/N10.bin" 234018 11
private theorem check10_713 : checkChunk 10 (table 10) (table 11) 713 row10_713 = true := by decide +kernel
private theorem good10_713 : GoodRange 10 713 724 :=
  chunk_sound 10 _ _ 713 row10_713 check10_713

private noncomputable def row10_724 : List Row := cert16Rows% "../Data/N10.bin" 236136 11
private theorem check10_724 : checkChunk 10 (table 10) (table 11) 724 row10_724 = true := by decide +kernel
private theorem good10_724 : GoodRange 10 724 735 :=
  chunk_sound 10 _ _ 724 row10_724 check10_724

private noncomputable def row10_735 : List Row := cert16Rows% "../Data/N10.bin" 238242 11
private theorem check10_735 : checkChunk 10 (table 10) (table 11) 735 row10_735 = true := by decide +kernel
private theorem good10_735 : GoodRange 10 735 746 :=
  chunk_sound 10 _ _ 735 row10_735 check10_735

private noncomputable def row10_746 : List Row := cert16Rows% "../Data/N10.bin" 240356 11
private theorem check10_746 : checkChunk 10 (table 10) (table 11) 746 row10_746 = true := by decide +kernel
private theorem good10_746 : GoodRange 10 746 757 :=
  chunk_sound 10 _ _ 746 row10_746 check10_746

private noncomputable def row10_757 : List Row := cert16Rows% "../Data/N10.bin" 242474 11
private theorem check10_757 : checkChunk 10 (table 10) (table 11) 757 row10_757 = true := by decide +kernel
private theorem good10_757 : GoodRange 10 757 768 :=
  chunk_sound 10 _ _ 757 row10_757 check10_757

private noncomputable def row10_768 : List Row := cert16Rows% "../Data/N10.bin" 244572 11
private theorem check10_768 : checkChunk 10 (table 10) (table 11) 768 row10_768 = true := by decide +kernel
private theorem good10_768 : GoodRange 10 768 779 :=
  chunk_sound 10 _ _ 768 row10_768 check10_768

private noncomputable def row10_779 : List Row := cert16Rows% "../Data/N10.bin" 246686 11
private theorem check10_779 : checkChunk 10 (table 10) (table 11) 779 row10_779 = true := by decide +kernel
private theorem good10_779 : GoodRange 10 779 790 :=
  chunk_sound 10 _ _ 779 row10_779 check10_779

private noncomputable def row10_790 : List Row := cert16Rows% "../Data/N10.bin" 248792 11
private theorem check10_790 : checkChunk 10 (table 10) (table 11) 790 row10_790 = true := by decide +kernel
private theorem good10_790 : GoodRange 10 790 801 :=
  chunk_sound 10 _ _ 790 row10_790 check10_790

private noncomputable def row10_801 : List Row := cert16Rows% "../Data/N10.bin" 250898 11
private theorem check10_801 : checkChunk 10 (table 10) (table 11) 801 row10_801 = true := by decide +kernel
private theorem good10_801 : GoodRange 10 801 812 :=
  chunk_sound 10 _ _ 801 row10_801 check10_801

theorem range10_0 : GoodRange 10 0 812 :=
  (joinRanges (joinRanges (joinRanges (joinRanges (joinRanges (joinRanges good10_0 (joinRanges good10_4 good10_7)) (joinRanges good10_11 (joinRanges good10_15 good10_19))) (joinRanges (joinRanges good10_23 (joinRanges good10_27 good10_31)) (joinRanges good10_35 (joinRanges good10_39 good10_45)))) (joinRanges (joinRanges (joinRanges good10_52 (joinRanges good10_61 good10_71)) (joinRanges good10_83 (joinRanges good10_95 good10_99))) (joinRanges (joinRanges good10_100 (joinRanges good10_101 good10_104)) (joinRanges (joinRanges good10_106 good10_107) (joinRanges good10_109 good10_112))))) (joinRanges (joinRanges (joinRanges (joinRanges good10_115 (joinRanges good10_117 good10_121)) (joinRanges good10_125 (joinRanges good10_129 good10_133))) (joinRanges (joinRanges good10_140 (joinRanges good10_147 good10_154)) (joinRanges good10_161 (joinRanges good10_168 good10_175)))) (joinRanges (joinRanges (joinRanges good10_182 (joinRanges good10_189 good10_198)) (joinRanges good10_208 (joinRanges good10_219 good10_230))) (joinRanges (joinRanges good10_240 (joinRanges good10_250 good10_261)) (joinRanges (joinRanges good10_271 good10_282) (joinRanges good10_293 good10_304)))))) (joinRanges (joinRanges (joinRanges (joinRanges (joinRanges good10_316 (joinRanges good10_327 good10_339)) (joinRanges good10_350 (joinRanges good10_361 good10_373))) (joinRanges (joinRanges good10_385 (joinRanges good10_396 good10_408)) (joinRanges good10_420 (joinRanges good10_432 good10_434)))) (joinRanges (joinRanges (joinRanges good10_436 (joinRanges good10_442 good10_445)) (joinRanges good10_447 (joinRanges good10_449 good10_456))) (joinRanges (joinRanges good10_459 (joinRanges good10_466 good10_477)) (joinRanges (joinRanges good10_488 good10_498) (joinRanges good10_509 good10_519))))) (joinRanges (joinRanges (joinRanges (joinRanges good10_531 (joinRanges good10_542 good10_553)) (joinRanges good10_565 (joinRanges good10_576 good10_587))) (joinRanges (joinRanges good10_598 (joinRanges good10_610 good10_621)) (joinRanges good10_633 (joinRanges good10_644 good10_656)))) (joinRanges (joinRanges (joinRanges good10_667 (joinRanges good10_679 good10_690)) (joinRanges good10_702 (joinRanges good10_713 good10_724))) (joinRanges (joinRanges good10_735 (joinRanges good10_746 good10_757)) (joinRanges (joinRanges good10_768 good10_779) (joinRanges good10_790 good10_801)))))))

end Ramsey556.Cert16
