import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template47 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 371569952044859
  lowerMask := 2417851638857688397367492

private def cap47_0Codes : List Nat := [
  94206147186]

def cap47_0 : Group.Batch template47.capOK :=
  Packed.capBatch template47 161792 rfl (by decide) cap47_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
