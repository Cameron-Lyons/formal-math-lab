import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template56 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 4804560284040763
  lowerMask := 2417851634424698065371588

private def cap56_0Codes : List Nat := [
  137678294386]

def cap56_0 : Group.Batch template56.capOK :=
  Packed.capBatch template56 161792 rfl (by decide) cap56_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
