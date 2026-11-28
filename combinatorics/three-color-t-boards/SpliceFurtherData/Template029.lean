import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template29 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11278484700151355
  lowerMask := 2417851627950773649260996

private def cap29_0Codes : List Nat := [
  1355771926]

def cap29_0 : Group.Batch template29.capOK :=
  Packed.capBatch template29 161792 rfl (by decide) cap29_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
