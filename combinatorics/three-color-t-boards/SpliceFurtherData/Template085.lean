import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template85 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2623404108691003
  lowerMask := 2417851636605854240721348

private def cap85_0Codes : List Nat := [
  420007397242, 422419076500]

def cap85_0 : Group.Batch template85.capOK :=
  Packed.capBatch template85 161792 rfl (by decide) cap85_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
