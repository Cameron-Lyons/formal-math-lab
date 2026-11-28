import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template26 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 9079465755950619
  lowerMask := 2417851630149792593461732

private def cap26_0Codes : List Nat := [
  1225230382, 4067180020]

def cap26_0 : Group.Batch template26.capOK :=
  Packed.capBatch template26 161792 rfl (by decide) cap26_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
