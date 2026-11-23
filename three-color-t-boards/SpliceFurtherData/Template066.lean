import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template66 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 371604311782971
  lowerMask := 2417851638857654037629380

private def cap66_0Codes : List Nat := [
  287515448977]

def cap66_0 : Group.Batch template66.capOK :=
  Packed.capBatch template66 161792 rfl (by decide) cap66_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
