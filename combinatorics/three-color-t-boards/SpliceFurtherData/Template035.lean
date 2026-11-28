import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template35 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4523360187332155
  lowerMask := 2417851634705898162080196

private def cap35_0Codes : List Nat := [
  5057271562, 141021766858, 381739030690]

def cap35_0 : Group.Batch template35.capOK :=
  Packed.capBatch template35 161792 rfl (by decide) cap35_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
