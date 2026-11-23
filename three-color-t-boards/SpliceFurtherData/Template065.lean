import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template65 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 283647677183515
  lowerMask := 2417851638945610672228836

private def cap65_0Codes : List Nat := [
  287472577702]

def cap65_0 : Group.Batch template65.capOK :=
  Packed.capBatch template65 161792 rfl (by decide) cap65_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
