import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template59 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9097328524801595
  lowerMask := 2417851630131929824610756

private def cap59_0Codes : List Nat := [
  141065701555, 392200271869]

def cap59_0 : Group.Batch template59.capOK :=
  Packed.capBatch template59 161792 rfl (by decide) cap59_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
