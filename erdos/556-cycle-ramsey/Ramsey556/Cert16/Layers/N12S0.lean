import Ramsey556.Cert16.Read
import Ramsey556.Cert16.Ranges
import Ramsey556.Cert16.Layers.N11

-- Generated from N12.bin, SHA-256 60541557e97dd9a8baed389e06d9d7e133c64c9e89503f0f191a5dd47ec8e03b.

namespace Ramsey556.Cert16

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option Elab.async false

private noncomputable def row12_0 : List Row := cert16Rows% "../Data/N12.bin" 0 2
private theorem check12_0 : checkChunk 12 (table 12) (table 13) 0 row12_0 = true := by decide +kernel
private theorem good12_0 : GoodRange 12 0 2 :=
  chunk_sound 12 _ _ 0 row12_0 check12_0

private noncomputable def row12_2 : List Row := cert16Rows% "../Data/N12.bin" 1668 4
private theorem check12_2 : checkChunk 12 (table 12) (table 13) 2 row12_2 = true := by decide +kernel
private theorem good12_2 : GoodRange 12 2 6 :=
  chunk_sound 12 _ _ 2 row12_2 check12_2

private noncomputable def row12_6 : List Row := cert16Rows% "../Data/N12.bin" 3464 7
private theorem check12_6 : checkChunk 12 (table 12) (table 13) 6 row12_6 = true := by decide +kernel
private theorem good12_6 : GoodRange 12 6 13 :=
  chunk_sound 12 _ _ 6 row12_6 check12_6

private noncomputable def row12_13 : List Row := cert16Rows% "../Data/N12.bin" 5590 8
private theorem check12_13 : checkChunk 12 (table 12) (table 13) 13 row12_13 = true := by decide +kernel
private theorem good12_13 : GoodRange 12 13 21 :=
  chunk_sound 12 _ _ 13 row12_13 check12_13

private noncomputable def row12_21 : List Row := cert16Rows% "../Data/N12.bin" 7822 8
private theorem check12_21 : checkChunk 12 (table 12) (table 13) 21 row12_21 = true := by decide +kernel
private theorem good12_21 : GoodRange 12 21 29 :=
  chunk_sound 12 _ _ 21 row12_21 check12_21

private noncomputable def row12_29 : List Row := cert16Rows% "../Data/N12.bin" 9858 8
private theorem check12_29 : checkChunk 12 (table 12) (table 13) 29 row12_29 = true := by decide +kernel
private theorem good12_29 : GoodRange 12 29 37 :=
  chunk_sound 12 _ _ 29 row12_29 check12_29

private noncomputable def row12_37 : List Row := cert16Rows% "../Data/N12.bin" 11898 6
private theorem check12_37 : checkChunk 12 (table 12) (table 13) 37 row12_37 = true := by decide +kernel
private theorem good12_37 : GoodRange 12 37 43 :=
  chunk_sound 12 _ _ 37 row12_37 check12_37

private noncomputable def row12_43 : List Row := cert16Rows% "../Data/N12.bin" 14046 8
private theorem check12_43 : checkChunk 12 (table 12) (table 13) 43 row12_43 = true := by decide +kernel
private theorem good12_43 : GoodRange 12 43 51 :=
  chunk_sound 12 _ _ 43 row12_43 check12_43

private noncomputable def row12_51 : List Row := cert16Rows% "../Data/N12.bin" 16150 9
private theorem check12_51 : checkChunk 12 (table 12) (table 13) 51 row12_51 = true := by decide +kernel
private theorem good12_51 : GoodRange 12 51 60 :=
  chunk_sound 12 _ _ 51 row12_51 check12_51

private noncomputable def row12_60 : List Row := cert16Rows% "../Data/N12.bin" 18392 4
private theorem check12_60 : checkChunk 12 (table 12) (table 13) 60 row12_60 = true := by decide +kernel
private theorem good12_60 : GoodRange 12 60 64 :=
  chunk_sound 12 _ _ 60 row12_60 check12_60

private noncomputable def row12_64 : List Row := cert16Rows% "../Data/N12.bin" 20160 8
private theorem check12_64 : checkChunk 12 (table 12) (table 13) 64 row12_64 = true := by decide +kernel
private theorem good12_64 : GoodRange 12 64 72 :=
  chunk_sound 12 _ _ 64 row12_64 check12_64

theorem range12_0 : GoodRange 12 0 72 :=
  (joinRanges (joinRanges (joinRanges good12_0 good12_2) (joinRanges good12_6 (joinRanges good12_13 good12_21))) (joinRanges (joinRanges good12_29 (joinRanges good12_37 good12_43)) (joinRanges good12_51 (joinRanges good12_60 good12_64))))

end Ramsey556.Cert16
