import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template45 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 89858754231835
  lowerMask := 2417851639139399595180516

private def cap45_0Codes : List Nat := [
  42249759490]

def cap45_0 : Group.Batch template45.capOK :=
  Packed.capBatch template45 161792 rfl (by decide) cap45_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
