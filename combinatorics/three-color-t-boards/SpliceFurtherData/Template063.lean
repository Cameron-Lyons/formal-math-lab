import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template63 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9361211313501755
  lowerMask := 2417851629868047035910596

private def cap63_0Codes : List Nat := [
  285980332279]

def cap63_0 : Group.Batch template63.capOK :=
  Packed.capBatch template63 161792 rfl (by decide) cap63_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
