import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template31 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2271530325653275
  lowerMask := 2417851636957728023759076

private def cap31_0Codes : List Nat := [
  3635851296, 11643958578]

def cap31_0 : Group.Batch template31.capOK :=
  Packed.capBatch template31 161792 rfl (by decide) cap31_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
