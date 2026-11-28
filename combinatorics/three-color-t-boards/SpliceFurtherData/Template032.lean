import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template32 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9079706274117403
  lowerMask := 2417851630149552075294948

private def cap32_0Codes : List Nat := [
  4067140656, 13968122682, 94207210626]

def cap32_0 : Group.Batch template32.capOK :=
  Packed.capBatch template32 161792 rfl (by decide) cap32_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
