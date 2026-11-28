import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template43 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2271564685391387
  lowerMask := 2417851636957693664020964

private def cap43_0Codes : List Nat := [
  34932214957, 283656168895]

def cap43_0 : Group.Batch template43.capOK :=
  Packed.capBatch template43 161792 rfl (by decide) cap43_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
