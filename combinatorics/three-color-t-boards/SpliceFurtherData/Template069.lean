import SplicePacked

-- Generated from splice_further.json by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceFurtherData
open Splice

def template69 : Group where
  k := 5
  pivot := [2, 2, 0, 1, 2, 2, 2, 1, 0, 2, 2]
  caps := []
  tails := []
  upperMask := 2605816217744923
  lowerMask := 2417851636623442131667428

private def cap69_0Codes : List Nat := [
  317347010824]

def cap69_0 : Group.Batch template69.capOK :=
  Packed.capBatch template69 161792 rfl (by decide) cap69_0Codes
    (by decide +kernel)

end TBoards.SpliceFurtherData
