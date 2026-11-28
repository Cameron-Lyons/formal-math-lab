import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template91 : Group where
  k := 5
  pivot := [2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1]
  caps := []
  tails := []
  upperMask := 593396351727131
  lowerMask := 2417851638635861997685220

private def cap91_0Codes : List Nat := [
  1225230382, 4067180020, 31444032852,
  137679357826, 282578603166, 283005332766,
  412000344684]

def cap91_0 : Group.Batch template91.capOK :=
  Packed.capBatch template91 150568 rfl (by decide) cap91_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
