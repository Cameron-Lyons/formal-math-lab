import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template82 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 11278763873023515
  lowerMask := 2417851627950494476388836

private def cap82_0Codes : List Nat := [
  418562939218]

def cap82_0 : Group.Batch template82.capOK :=
  Packed.capBatch template82 161792 rfl (by decide) cap82_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
