import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template54 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9026929716377371
  lowerMask := 2417851630202328633034980

private def cap54_0Codes : List Nat := [
  137593264602, 388727834916]

def cap54_0 : Group.Batch template54.capOK :=
  Packed.capBatch template54 161792 rfl (by decide) cap54_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
