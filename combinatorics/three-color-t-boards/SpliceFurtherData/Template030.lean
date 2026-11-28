import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template30 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4523055244656411
  lowerMask := 2417851634706203104755940

private def cap30_0Codes : List Nat := [
  3635844759]

def cap30_0 : Group.Batch template30.capOK :=
  Packed.capBatch template30 161792 rfl (by decide) cap30_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
