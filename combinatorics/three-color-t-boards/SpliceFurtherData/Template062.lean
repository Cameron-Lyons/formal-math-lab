import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template62 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2623369748952891
  lowerMask := 2417851636605888600459460

private def cap62_0Codes : List Nat := [
  285964946895]

def cap62_0 : Group.Batch template62.capOK :=
  Packed.capBatch template62 161792 rfl (by decide) cap62_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
