import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template28 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9097053646896699
  lowerMask := 2417851630132204702515652

private def cap28_0Codes : List Nat := [
  1226292778]

def cap28_0 : Group.Batch template28.capOK :=
  Packed.capBatch template28 161792 rfl (by decide) cap28_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
