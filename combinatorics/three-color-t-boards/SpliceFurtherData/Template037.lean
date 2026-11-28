import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template37 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9097023582125851
  lowerMask := 2417851630132234767286500

private def cap37_0Codes : List Nat := [
  15286923288]

def cap37_0 : Group.Batch template37.capOK :=
  Packed.capBatch template37 161792 rfl (by decide) cap37_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
