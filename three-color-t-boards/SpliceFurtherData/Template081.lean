import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template81 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4593458348047899
  lowerMask := 2417851634635800001364452

private def cap81_0Codes : List Nat := [
  418559746141, 420007037131]

def cap81_0 : Group.Batch template81.capOK :=
  Packed.capBatch template81 161792 rfl (by decide) cap81_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
