import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template15 : Group where
  k := 5
  pivot := [0, 2, 1, 0, 1, 1, 2, 1, 0, 0, 2]
  caps := []
  tails := []
  upperMask := 37788322149999745255391
  lowerMask := 2380063317079258604156960

private def cap15_0Codes : List Nat := [
  283669410229, 290614281217, 294086716711,
  301031587699]

def cap15_0 : Group.Batch template15.capOK :=
  Packed.capBatch template15 47090 rfl (by decide) cap15_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
