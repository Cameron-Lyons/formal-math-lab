import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template34 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 301235568129595
  lowerMask := 2417851638928022781282756

private def cap34_0Codes : List Nat := [
  5056208662]

def cap34_0 : Group.Batch template34.capOK :=
  Packed.capBatch template34 161792 rfl (by decide) cap34_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
